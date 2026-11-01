#!/usr/bin/env bash
# patch/gen_corpus.sh, run in a tree of the project (`tools/qp tree zstd` in a QuickProof workspace): regenerate harness/corpus.h
# with the upstream compressor of the tree's lib/ (env.c's frames).
set -euo pipefail
cd "$(dirname "$0")/.."
B=build/corpus; mkdir -p $B
{
  for f in common/debug.c common/entropy_common.c common/error_private.c common/fse_decompress.c common/xxhash.c \
           common/zstd_common.c compress/fse_compress.c compress/hist.c compress/huf_compress.c \
           compress/zstd_compress_literals.c compress/zstd_compress_sequences.c compress/zstd_compress_superblock.c \
           compress/zstd_preSplit.c compress/zstd_compress.c compress/zstd_double_fast.c compress/zstd_fast.c \
           compress/zstd_lazy.c compress/zstd_ldm.c compress/zstd_opt.c decompress/huf_decompress.c \
           decompress/zstd_ddict.c decompress/zstd_decompress.c decompress/zstd_decompress_block.c; do
    echo "#include \"$PWD/lib/$f\""
  done
} > $B/unity.c
gcc -O1 -w -DZSTD_DISABLE_ASM -Ilib -Ilib/common $B/unity.c patch/gen_corpus.c -o $B/gen_corpus
$B/gen_corpus
