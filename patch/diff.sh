#!/usr/bin/env bash
# patch/diff.sh [CASES], run in the patched tree (`tools/qp tree zstd`): the differential test of the idiom
# patch.  The unmodified upstream library ($ORIG, default: the tree of `tools/qp tree zstd --orig`, plus patch/fixes.py; compressor
# and decoder in one translation unit, symbols renamed orig_* with objcopy) against the patched decoder,
# both with the flags of genproof.conf, under ASan/UBSan (patch/diff_decompress.c).
set -euo pipefail
cd "$(dirname "$0")/.."
CASES=${1:-20000}
ORIG=${ORIG:-$HOME/zstd-orig/lib}
INC=(); DEFS=(); UNITS=(); GP=$PWD/genproof; source genproof.conf
B=build/diff; mkdir -p $B
# The bug fixes (patch/fixes.py) change behaviour on purpose: apply them to the original too, so that this test
# compares exactly the idiom and VST layers (which must change nothing).
if [ -f patch/fixes.py ]; then
  rm -rf $B/origtree && mkdir -p $B/origtree && cp -r "$ORIG" $B/origtree/lib
  (cd $B/origtree && python3 "$OLDPWD/patch/fixes.py")
  ORIG=$PWD/$B/origtree/lib
fi
SAN=(-fsanitize=address,undefined -fno-sanitize-recover=all)
CF=(-O1 -g -w "${SAN[@]}" "${DEFS[@]}")
unity() {   # unity DIR FILES...: one translation unit including DIR/FILES
  local d=$1; shift
  for f in "$@"; do echo "#include \"$d/$f\""; done
}
DEC=(common/debug.c common/entropy_common.c common/error_private.c common/fse_decompress.c common/xxhash.c
     common/zstd_common.c decompress/huf_decompress.c decompress/zstd_ddict.c decompress/zstd_decompress.c
     decompress/zstd_decompress_block.c)
COMP=(compress/fse_compress.c compress/hist.c compress/huf_compress.c compress/zstd_compress_literals.c
      compress/zstd_compress_sequences.c compress/zstd_compress_superblock.c compress/zstd_preSplit.c
      compress/zstd_compress.c compress/zstd_double_fast.c compress/zstd_fast.c compress/zstd_lazy.c
      compress/zstd_ldm.c compress/zstd_opt.c)
unity "$(realpath "$ORIG")" "${DEC[@]}" "${COMP[@]}" > $B/orig_unity.c
unity "$PWD/lib" "${DEC[@]}" > $B/patched_unity.c
gcc "${CF[@]}" -I"$ORIG" -I"$ORIG/common" -c $B/orig_unity.c -o $B/orig.o
gcc "${CF[@]}" -I"$ORIG" -DORIG -c patch/diff_run.c -o $B/run_orig.o
ld -r $B/orig.o $B/run_orig.o -o $B/orig_all.o
nm --defined-only -g $B/orig_all.o | awk '$3 !~ /^(dt_compress|dt_bound|orig_)/ {print $3" orig_"$3}' > $B/orig.syms
objcopy --redefine-syms=$B/orig.syms $B/orig_all.o
gcc "${CF[@]}" -Ilib -Ilib/common -c $B/patched_unity.c -o $B/patched.o
gcc "${CF[@]}" -Ilib -c patch/diff_run.c -o $B/run_patched.o
gcc "${SAN[@]}" -O1 -g patch/diff_decompress.c $B/orig_all.o $B/patched.o $B/run_patched.o -o $B/diff_decompress
# Every allocation filled with zeros (ASan fills only the first 4 KiB by default): on corrupt input the
# decoder copies bytes of its own never-written buffers into dst before it reports the error, and those
# bytes would differ between the two decoders' allocations (an upstream behaviour, not the patch).
ASAN_OPTIONS=detect_leaks=0:max_malloc_fill_size=2147483647:malloc_fill_byte=0 $B/diff_decompress "$CASES"
