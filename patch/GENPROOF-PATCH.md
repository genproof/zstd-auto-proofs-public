# Changes to zstd's decoder

`lib/` holds zstd 01b7154f1172 with the changes described here. The scripts in this directory made them, in this
order: `zstdpatch.py`, `vstpatch.py`, `fixes.py`, `fixes2.py`, `fixes3.py`, `fixes4.py`, `fixes5.py`,
`lawhooks.py`. They edit files in place, so do not run them on this tree. Many changed lines carry a comment with
the original, tagged `genproof` (the idiom edits and the fixes of `fixes.py`) or with its F-number.

- The idiom edits (`zstdpatch.py`, items 1-20, and the VST layer, `vstpatch.py`) rewrite C that CompCert's
  semantics or VST cannot handle, such as comparing pointers into different objects or copying structs. They
  change no result zstd documents. The differential test against the original found no difference on the edits it
  was run on (each item gives its evidence); that is a test, not a proof. Items 18 and 20 change what a failed
  decode leaves in the context and in dst.
- The changes F1-F8 (`fixes.py`, `fixes2.py`) change results.
- F9 to F12 (`fixes3.py`, `fixes4.py`, `fixes5.py`) remove expressions that CompCert's semantics leaves undefined or
  that VST cannot type, and bound one loop ([docs/fixes-F9-F12.md](../docs/fixes-F9-F12.md)).
- H1 (`lawhooks.py`) adds one function.

## The idiom edits (`zstdpatch.py`)

zstd's decoder (lib/common and lib/decompress) has undefined behaviour in CompCert's C semantics, the semantics of
every QuickProof theorem, on ordinary valid frames: CompCert's interpreter stops on the first frame of any test.
Native builds are fine, and ASan and UBSan see nothing. Nine of the eleven idioms below are undefined in ISO C too
(pointer arithmetic or comparison outside an object, or across objects; NULL - NULL); of the other two, one is
implementation-defined and one defined in ISO C, and neither has a meaning in CompCert. So "ZSTD_decompress has no
undefined behaviour on any input" cannot be proved for the code as it is.

They were found with CompCert 3.15's interpreter (`ccomp -interp`), one stop at a time, and by proof attempts (the
interpreter cannot see a pointer up to 8 bytes before a heap block: its `malloc` keeps an 8-byte header there,
which VST's `malloc_spec'` does not give):

| where | idiom | ISO C | reached by |
|---|---|---|---|
| `ZSTD_decompressFrame` | in-place test `ip >= op && ip < oBlockEnd`: orders pointers into src and dst | undefined (different objects) | every block |
| `ZSTD_checkContinuity`, `ZSTD_refDictContent` | `previousDstEnd - prefixStart` while both are NULL | undefined (NULL - NULL) | the first block of a fresh context; every dictionary load |
| `ZSTD_wildcopy`, `ZSTD_safecopy` | `dst - src` / `op - ip` computed before knowing they are in one object | undefined (different objects) | every literal copy |
| `ZSTD_execSequence`, `ZSTD_execSequenceSplitLitBuffer` | `oMatchEnd = op + sequenceLength`, `iLitEnd = *litPtr + litLength` formed, then compared | undefined (past the end) | any dst too small for a sequence |
| `BIT_reloadDStream`, `BIT_reloadDStreamFast` | limit pointer `limitPtr = start + 8` compared | undefined (past the end) | any bitstream shorter than 8 bytes at the end of the input |
| `XXH64_update` (the frame checksum) | `p + 32 <= bEnd`: a pointer past the end of a short input | undefined (outside the object) | a checksummed frame whose last chunk is short |
| `ZSTD_decompressBlock_internal` | `totalHistorySize = dst + blockSizeMax - virtualStart` while `virtualStart` is still NULL | undefined (pointer minus NULL) | a compressed block with output capacity 0 (found by a proof attempt) |
| `ZSTD_safecopy`, `ZSTD_safecopyDstBeforeSrc` | `oend <= oend_w`, `op <= oend_w`, `op <= oend - 32`: a limit before a short output | undefined (outside the object) | a sequence near the end of an output shorter than 32 bytes (found by the interpreter) |
| `BIT_reloadDStream`, the cautious update | `ptr - nbBytes < start`: a pointer up to 7 bytes before the bitstream | undefined (before the object) when the stream starts within 7 bytes of its buffer: streaming, a block at offset 0 of inBuff or of an input chunk (found by a proof attempt) | a block with a tiny literals section, streamed |
| `ZSTD_decompressBlock_internal` | `(size_t)(-1) - (size_t)dst < 1 MiB`: address arithmetic | implementation-defined | every compressed block |
| `ZSTD_checkContinuity` with a dictionary | `dst != previousDstEnd`, a one-past-the-end pointer of the dictionary vs another object | defined | every decoding with a raw dictionary |

`zstdpatch.py` (6 files) rewrites the ones undefined in ISO C as distances inside one object, with the same result
whenever the original is defined:

| before | after |
|---|---|
| `ip >= op && ip < oBlockEnd` | `GP_INPLACE(ip, op, oBlockEnd)`: the original by default; `0` in `quickproof.conf` (src and dst separate objects, where the original is always false) |
| `x - (previousDstEnd - prefixStart)` | `x - (previousDstEnd == NULL ? 0 : previousDstEnd - prefixStart)` (2 sites) |
| `ptrdiff_t diff = dst - src;` up front | computed only in the overlapping branch (2 functions; the asserts on it dropped) |
| `iLitEnd > litLimit`, `oMatchEnd > oend_w` | `litLimit - *litPtr < (ptrdiff_t)litLength`, `oend_w - op < (ptrdiff_t)sequenceLength` (2 functions) |
| `bitD->ptr < / >= bitD->limitPtr` | `(size_t)(bitD->ptr - bitD->start) < / >= sizeof(bitD->bitContainer)` |
| xxhash: `p+32 <= bEnd` | `(size_t)(bEnd - p) >= 32` (XXH32's `p <= bEnd-16` is the same idiom, but the decoder does not use XXH32) |
| `totalHistorySize = ZSTD_totalHistorySize(dst + ..., virtualStart)` | `dstCapacity == 0 ? 0 : ...` (the value is dead then: used on 32-bit only, or after the `dstCapacity == 0 && nbSeq > 0` error) |
| `oend <= oend_w`, `op <= oend_w`, `op <= oend - WILDCOPY_OVERLENGTH` | `oend_w - oend >= 0`, `oend_w - op >= 0`, `oend - op >= WILDCOPY_OVERLENGTH` |
| `bitD->ptr - nbBytes < bitD->start` | `(size_t)(bitD->ptr - bitD->start) < nbBytes` (here `0 < ptr - start < 8`) |
| `(size_t)(-1) - (size_t)dst < (1 << 20)` | `GP_DST_NEAR_TOP(dst)`: the original by default; `0` in `quickproof.conf` (no object lies in the top MiB of CompCert's offsets) |

The last row of the first table cannot be rewritten in C: CompCert gives `==` between a one-past-the-end
pointer and a pointer into another object no meaning. A spec that decodes with a dictionary must carve
the dictionary and dst from one object (checked: then the dictionary path runs).

**Item 13**: `match + sequence.matchLength <= dictEnd` in the four sequence executors (a match from the dictionary
running on into dst) and `dictPtr+12 > dictEnd` in `ZSTD_loadDEntropy` (a truncated formatted dictionary) form
pointers past the dictionary's object; now signed distances (`dictEnd - match >= (ptrdiff_t)sequence.matchLength`,
`dictEnd - dictPtr < 12`). diff.sh 140,000 runs, 0 mismatches; the interpreter inputs that stopped no longer stop.

**Item 14**: `ip+2 > iend` (nbSeq byte 0xFF) and `ip+1 > iend` in `ZSTD_decodeSeqHeaders` form pointers past the end
of the input when the input ends inside or right after the nbSeq field; now `iend - ip < 2`, `iend - ip < 1`
(`ip <= iend` holds at both). diff.sh 140,000 runs, 0 mismatches; the interpreter input that stopped no longer
stops.

**Item 15**: `ip + (bitCount>>3) <= iend-4` in `FSE_readNCount_body` (`lib/common/entropy_common.c`, now a sixth
patched file) forms a pointer up to `iend + 1` when an FSE table description ends its object and the reader is
clamped to its last 4 bytes (reachable after a count; after a run of zeros `bitCount <= 34`); now
`(bitCount>>3) <= (iend-4) - ip` at both sites. diff.sh 140,000 runs, 0 mismatches; the interpreter input that
stopped no longer stops.

**Item 16**: `litPtr + litLength > dctx->litBufferEnd` in the split-literals loops
(`ZSTD_decompressSequences_bodySplitLitBuffer`, twice in `ZSTD_decompressSequencesLong_body`) forms a pointer far
past the output buffer when a sequence's literal length (up to 131071) exceeds what is left; now
`(size_t)(dctx->litBufferEnd - litPtr) < litLength` at the three sites. diff.sh 140,000 runs, 0 mismatches; the
interpreter input that stopped no longer stops.

**Item 17**: the decoder context (`ZSTD_createDCtx_internal`) and the streaming buffers (`ZSTD_decompressStream`)
come from `ZSTD_customCalloc` instead of `ZSTD_customMalloc`. `ZSTD_copy16` and the wildcopies read past a
sequence's literals into never-written bytes of `litExtraBuffer`; in buffered streaming after a ring wrap, a match
into the extDict window (the same ring) can copy that slack into the regenerated content, which the frame checksum
hashes: arithmetic on never-written bytes, undefined in CompCert's semantics (spec `x_any_stream`). Not undefined
in ISO C, so an inconsistency, not a bug. Zeroed memory gives the same results on every frame that reads no
never-written byte; the differential test fills every allocation with 0 anyway, so it sees no difference by
construction.

**Item 18**: in `ZSTD_decodeLiteralsBlock`'s compressed-literals case with literals split between dst and the
context, the copy of the last `ZSTD_LITBUFFEREXTRASIZE` decoded bytes into `dctx->litExtraBuffer` ran before the
Huffman error check, so a failed decode filled the context's buffer with bytes of dst it never wrote (undoing item
17 for later use of the context). The copy now runs only after a successful decode
(`if (!HUF_isError(hufSuccess))`). On success nothing changes; on an error the same error code and the same dst
(the memmove inside dst still runs); `litExtraBuffer` keeps its previous bytes. Moving the error check up instead
would also skip that memmove and change dst after errors. No undefined behaviour in ISO C and no result changes.

**Evidence that the patch changes nothing observable** (the configuration of `quickproof.conf`):
- differential test (`diff.sh`): upstream library vs the patched decoder in one binary, under ASan/UBSan:
  140,000 runs (20,000 cases: frames of the upstream compressor at levels -5..19, with and without
  checksum and content size, two frames, raw-content dictionaries; valid, bit-flipped, overwritten,
  truncated and spliced; random bytes; exact, smaller and larger capacities; one-shot, streaming with
  random chunk sizes, dictionary decoding): identical results and identical whole output buffers in every
  run (63,098 successful decodes). A mutant of the patch (`< WILDCOPY_VECLEN` to `< 8`) gives 62
  mismatches in 700 runs, so the test does see differences. `diff.sh` records how the test was run; it does not
  run in this tree unchanged;
- CompCert's interpreter (zstd 01b7154f): the original stops on the first valid frame; the patched decoder runs 17
  valid frames (empty, raw, RLE, Huffman literals, 2 blocks, 2 frames + skippable, checksums) at exact and half
  capacity, the same frames streamed in 7-byte chunks, 80 mutated frames at two capacities, and a dictionary
  frame, with results equal to the native build of the original; `qp interp` ran the first two specs (30 seeds
  each) without a stop, with an earlier version of the framework whose memcpy copied any byte as it is (QuickProof
  v0.1.0's does not: [below](#the-framework-part-memcpy-and-memmove)).

**Upstream behaviour seen on the way** (not a patch difference): on corrupt input `ZSTD_decompress` can
return an error after copying bytes of its own never-written buffers (the over-copied slack of the
literal buffer) into the caller's dst. The differential test fills every allocation (`malloc_fill_byte=0`)
to compare only what the patch can change; with ASan's default fill (first 4 KiB only) the two decoders
leave different bytes in dst in 221 of 140,000 runs, all on errors.

## The VST layer (`vstpatch.py`, after `zstdpatch.py`)

VST has no rule for assigning a struct ("Verifiable C does not support assignment to variables of struct or
union type"), and QuickProof's `clight.sh` (clightgen without `-fstruct-passing`) rejects struct parameters and
returns: 91 sites in the decoder (zstd_decompress.c 42, zstd_decompress_block.c 26, huf_decompress.c 13,
zstd_ddict.c 7, common/allocations.h 3), and about 45 struct assignments behind them. The second layer (10 files)
removes them all, and nothing else:

| struct | before | after |
|---|---|---|
| `seq_t` | by value into `ZSTD_execSequence{,End}{,SplitLitBuffer}`, `ZSTD_prefetchMatch`; returned by `ZSTD_decodeSequence`; `sequences[i] = sequence` | `const seq_t*`, the callee copying it field by field into a local (it modifies its copy, as before); out-pointer; `ZSTD_seqCopy` |
| `ZSTD_customMem` | by value into the allocation helpers, the DDict hash set, `ZSTD_createDCtx_internal`; copied into contexts | `const ZSTD_customMem*` (`ZSTD_customMallocP`/`CallocP`/`FreeP`, `ZSTD_createDDict_advancedP`); `ZSTD_customMem_copy` |
| `ZSTD_frameSizeInfo`, `ZSTD_bounds`, `ZSTD_OffsetInfo`, `DTableDesc` | returned | out-pointers (`ZSTD_dParam_getBoundsP`, `HUF_getDTableLog` for `.tableLog`) |
| `HUF_DEltX2` | returned by `HUF_buildDEltX2`, then copied into the table | built in place, into each table entry |
| `HUF_DEltX1`, `FSE_decode_t` | `dt[u] = D`; `DInfo = table[state]` | field by field (`FSE_decode_copy`) |
| `ZSTD_outBuffer` | `zds->expectedOutBuffer = *output`; `expect = zds->expectedOutBuffer` | `ZSTD_outBuffer_copy`; read through a pointer (below) |

Public functions with a struct parameter or return keep their API on top of the pointer versions, and the
verified configuration leaves them out (`GP_NO_STRUCT_API`): `ZSTD_createDCtx_advanced`,
`ZSTD_createDStream_advanced`, `ZSTD_createDDict_advanced`, `ZSTD_dParam_getBounds`; so are the by-value
allocation helpers, which the (unverified) compressor still uses. The layer also ends the `default` block of
`HUF_fillDTableX2Level2` with `break` (VST's switch rule gives a case that falls off the end of a switch the
postcondition `FF`), and casts `BIT_initDStream`'s `switch(srcSize)` to `unsigned` (VST's switch rule needs an `int`
scrutinee; there `srcSize < 8`, so the cast is exact).

**A copied dictionary.** After `ZSTD_createDDict` or `ZSTD_DCtx_loadDictionary`, zstd's `previousDstEnd` is the end
of its own copy of the dictionary, and `ZSTD_checkContinuity` compares the output with it
(`dst != dctx->previousDstEnd`): one past the end of another object, which ISO C compares and CompCert's semantics
does not. The layer adds a flag `gpDictCopy` to the context, set by `ZSTD_copyDDictParameters` for a DDict made by
copy and cleared wherever `previousDstEnd` is set otherwise, and skips the comparison while it is set: the output is
never contiguous with zstd's private copy (were it adjacent by chance, both paths read the same dictionary bytes).
Checked by `diff.sh`, which also decodes with a copied dictionary (`dt_ddict`): 140,000 runs, 0 mismatches.

**Only what VST needs.** The layer changes nothing else. An edit in a function that no spec reaches (its
specification in the proof is vacuous, its body is never verified) is left out, unless clightgen cannot translate
the file without it (struct parameters and returns). So the empty `default:;` of `ZSTD_DCtx_setParameter`,
`ZSTD_DCtx_getParameter` and `ZSTD_dParam_getBounds`, XXH32's `p <= bEnd - 16`, and XXH32_finalize's switch on a
`size_t` stay as they are. A `RETURN_ERROR` at the end of a switch case needs no `break` either: the macro is a
`do { ...; return e; } while (0)`, which cannot fall through, and `qp check`'s lint knows it.

A field-by-field copy is *stricter* than a struct copy in CompCert's semantics: it reads every field, and an
unwritten one is stuck, where the struct copy copied it as it is. Every copy above has a fully written source,
except `ZSTD_checkOutBuffer`'s, whose source is unwritten on the first call and read only later: that one reads
through a pointer instead (the interpreter found it; the native differential test cannot).

**MEM_write64 as byte stores.** VST's `mapsto tulong (Vlong x)` also holds of eight *fragments* of the value
(`decode_val Mint64` reassembles them on a 64-bit target), and each fragment reads back as an undefined byte;
so after `memcpy(p, &value, 8)` no specification can give the bytes of `value` (2- and 4-byte scalars are fine).
The decoder writes U64s with `MEM_write64` into byte tables (the FSE spread in `FSE_buildDTable_internal` and
`ZSTD_buildFSETable_body`, the Huffman X1 table in `HUF_readDTableX1_wksp`) and reads them back as bytes. The
layer makes `MEM_write64` eight little-endian byte stores (the native order of the verified x86-64 target; a
big-endian target keeps the copy). Not a zstd bug: a limit of the logic.

After the layer, the Clight of the decoder has no struct assignment, parameter or return, no switch case that
falls off the end, `goto` only in the fast Huffman loops (`HUF_DISABLE_FAST_DECODE`: unreachable), and
pointer-to-integer casts only in the static-allocation API and behind `XXH_FORCE_ALIGN_CHECK` (0).

**Huffman X2 table fill as U32 copies** (`huf_decompress.c`, `HUF_fillDTableX2ForWeight` cases 4, 8 and default,
the skip fill of `HUF_fillDTableX2Level2`): two cells were built in a `U64` and copied with an 8-byte `memcpy`; VST
cannot read the bytes or fields of a stored `U64` back, and the destination (4 mod 8) is not even 8-aligned for a
`tulong` copy. Now the cell is a `U32` (`HUF_buildDEltX2U32`) copied twice, to cells `j` and `j + 1`: the same bytes
on either endianness (the `U64` was the cell twice). Evidence: diff.sh 280,000 runs, 0 mismatches; 128 real zstd
frames (CLI levels 1-19) decode byte-exact, with every rewritten line executed but the skip fill for
`skipSize == 1`. `qp check` lints this class (`u64_copy_lint`).

**`ZSTD_checkContinuity` tests `dstSize > 0` first**: when a frame filled the output exactly, the next frame's `dst`
is one past the end of the output, and with a 0-byte copied dictionary `previousDstEnd` points into another object;
ISO C defines that `!=`, CompCert does not. The two operands are side-effect-free, so the reordered `&&` has the
same value; with `dstSize > 0`, `dst` is strictly inside the output. diff.sh 140,000 runs, 0 mismatches. Not a
zstd bug.

**`HUF_decodeStreamX2`: `(size_t)(pEnd - p) > 9`**: `p < pEnd-9` with `pEnd - p == 8` forms `p - 1`; when the
literal buffer starts a struct field (`litExtraBuffer`), VST needs ownership of the byte before it. `p <= pEnd`
holds there, so the distance test is the same. diff.sh 140,000 runs, 0 mismatches. Not a zstd bug (in zstd's own
use the buffer never starts an allocation there).

**`ZSTD_prefetchMatch`: no prefetch address from NULL**: the address
`ZSTD_wrappedPtrSub(ZSTD_wrappedPtrAdd(matchBase, pos), offset)` is `NULL + pos` when `matchBase` is a NULL `dictEnd`
(no dictionary). zstd does this on purpose (`compiler.h`: "Zstd relies on pointer overflow in its decompressor",
`ZSTD_ALLOW_POINTER_OVERFLOW_ATTR`; only a hint) and CompCert defines it, but VST cannot type pointer arithmetic on
NULL. The address is now computed only when `matchBase != NULL` (this build's `PREFETCH_L1` does nothing with it;
the wrapped-pointer helpers stay in the Clight, so their proofs stay valid). Documented upstream.

**The sequence executors' byte copies as one-byte `ZSTD_memmove`**: `ZSTD_overlapCopy8`'s first four bytes
(`(*op)[k] = (*ip)[k]`) and the short and leftover loops of `ZSTD_safecopy` and `ZSTD_safecopyDstBeforeSrc`
(`while (op < oend) *op++ = *ip++;`) copy each byte through an `unsigned char` temp, and VST's load rule needs a
defined byte there. For any input these copies can read bytes never written (wildcopy's over-copied slack in the
literal buffer and in the output, the streaming ring buffer after it wraps): defined in ISO C and in CompCert (the
byte stays undefined), unprovable in VST. Each byte is now copied with `ZSTD_memmove(dst, src, 1)`. memmove, not
memcpy: `ZSTD_safecopyDstBeforeSrc`'s loop runs for any `diff > -8`, `op == ip` included
(`ZSTD_execSequenceEndSplitLitBuffer` rejects only `op > *litPtr`), where a memcpy would be undefined. The same byte
moves, one at a time and forwards, so overlapping copies keep their order. memmove is already an external of the
Clight: no definition added or removed. No undefined behaviour in C.

**`&` before function designators in the HUF 4-stream wrappers**: `HUF_decompress4X1/4X2_usingDTable_internal`
initialise and assign their function-pointer locals with bare function designators
(`fallbackFn = HUF_..._default`), which Clight keeps as an Sset of an expression of function type, for which VST
has no rule. The address is taken explicitly at the 6 sites that reach the Clight (the asm-loop assignments are
compiled out): the same pointer in C. No Clight definition added or removed; the Ssets now hold
`Eaddrof (Evar ...)`.

**`ddictIsCold` without comparing pointers into two objects** (spec `x_any_params`):
`ZSTD_decompressBegin_usingDDict` set `dctx->ddictIsCold = (dctx->dictEnd != dictEnd)`, `dictEnd` being one past
the DDict's content. After a streaming ring wrap, `ZSTD_checkContinuity` leaves `dctx->dictEnd` in the output
buffer (and after another DDict, in that DDict), so the next frame's begin compares pointers into two objects, one
of them one past its end: defined in ISO C (6.5.9p6), but in CompCert's semantics a comparison across blocks needs
both pointers strictly valid, so the theorem's semantics is stuck. The flag only drives prefetch hints and, for the
first block, the choice between the equivalent long and short sequence decoders (`usePrefetchDecoder`), so it is
now set to 1 ("cold", as on a new context) without the comparison. Results are the same: `diff.sh` 100,000 cases
(700,000 runs, 356,329 successful decodes), 0 mismatches, with its DDict case now decoding twice with the same DDict
("hot" in the original, so the short decoder there and the long one here). This also removes, in this
configuration, upstream's comparison with the end of a possibly freed dictionary (PROMISES.md, "What the laws
found"); the specs still keep dictionaries alive. No undefined behaviour in C.

**Evidence** (the two layers together): `diff.sh` 140,000 runs, 0 mismatches; the interpreter set above (17 valid
frames at two capacities, streamed in 7-byte chunks, 80 mutated frames at two capacities, a dictionary frame)
identical to the native build of the original; `qp interp` 30 seeds of each of the first two specs without a stop
(with that earlier memcpy); `clight.sh` accepts every unit; their contracts build (`QPlink` of all units).

## The framework part: memcpy and memmove

zstd copies 16 bytes at a time past the literals it has written (`ZSTD_copy16` over the literal buffer's
slack), and after a Huffman error in split-literals mode `ZSTD_decodeLiteralsBlock` memmoved output bytes the
decode never wrote. That is legal C, but a byte loop through `unsigned char`, as `libc/libc.c`'s memcpy and memmove
are, cannot copy a never-written byte in CompCert's semantics: the copy is stuck.

QuickProof's memcpy and memmove are byte loops (`quickproof/libc/libc.c`), verified with the code, so the decoder
must never copy a byte it did not write; items 19 and 20 (in `zstdpatch.py`) make it so.

**Item 19**: `ZSTD_allocateLiteralsBuffer` zeroes the `WILDCOPY_OVERLENGTH` bytes after the literals when they go
into dst: the whole literal buffer after the block's output (`ZSTD_in_dst`), or the head of a split buffer at the
end of the block's output when the literals are copied or set at once (`splitImmediately`). The sequence executors'
`ZSTD_copy16` and wild copies read up to 16 bytes past a sequence's literals, so with the literals at the end of
the buffer they read bytes of dst that nothing wrote. Seen natively with MemorySanitizer and a checking
memcpy/memmove (specs `x_any_stream` and `x_any_params`: the single-pass shortcut of `ZSTD_decompressStream` into
the caller's buffer; and one-shot decoding of a frame whose last sequence ends within 16 bytes of the literals,
into a buffer more than a block larger than the content). zstd up to v1.4.x zeroed the same bytes
(`memset(dctx->litBuffer + dctx->litSize, 0, WILDCOPY_OVERLENGTH)`). Results are the same: the zeroed bytes lie
past the block's literals and are only ever over-read; in dst they lie beyond the block's output or are
overwritten by it. The literal buffer in the context needs nothing (item 17), nor literals read in place from the
input, nor a Huffman-decoded split buffer (after its shift, its slack holds decoded bytes).

**Item 20**: in `ZSTD_decodeLiteralsBlock`'s compressed-literals case with literals split between dst and the
context, the shift of the dst part (`ZSTD_memmove`) ran before the Huffman error check too, so after a failed decode
it moved bytes of dst that the decode never wrote. Like the copy of item 18, the shift now runs only after a
successful decode. On success nothing changes; on an error the same error code, and dst keeps the bytes the decode
left (dst is unspecified after an error).

Evidence: with both items, MemorySanitizer with a memcpy/memmove that checks its source finds no never-written
byte in 3,000 native runs of each of the 19 `x_` specs, nor in the frames that showed it before; without them,
`x_any_stream` and `x_any_params` show it within 2,000 runs. CompCert's interpreter on QuickProof v0.1.0-beta.1
(`qp interp`, its libc's byte loops) runs every spec without a stop.

## Changes F1-F4 (`fixes.py`, after the VST layer)

These change zstd's behaviour, so that every spec holds.
- F1: `ZSTD_getDictID_fromFrame` returns 0 for a skippable frame ("This is not a Zstandard frame"), instead of the
  magic variant that `ZSTD_getFrameHeader` reports in `dictID`.
- F2: while `ZSTD_decompressStream` loads a frame header, its hint never asks for more than the frame can still
  hold: before the magic number is complete, at most 8 bytes in all (an empty skippable frame, the shortest
  frame); in a skippable frame, the rest of its 8-byte header (no block header follows); in a Zstandard frame, the
  original formula.
- F3: the single-pass shortcut of `ZSTD_decompressStream` is taken only when the whole frame header came in the same
  call, so that the input it parses from the call's start is the frame's start (`zstd.h`: the frame's content is
  decoded, not bytes in the middle of the frame).
- F4: one-shot decoding with `ZSTD_d_refMultipleDDicts` loads the DDict that matches the frame's dictionary ID, as
  streaming decoding does ("the appropriate dictID is selected from the set of DDicts based on the dictID in the
  frame").

## Changes F5-F8 (`fixes2.py`, after `fixes.py`)

The short specs (written from RFC 8878 and `zstd.h`) need four more changes; `fixes2.py` makes them, each
replacement asserted to match once, each changed line marked with its F-number:

- F5 (specs `rfc_skippable`, `api_frame_size`): `readSkippableFrameSize` refused skippable frames whose
  `Frame_Size` is 2^32 - 8 or more (a 32-bit sum that would wrap), although RFC 8878 3.1.2 allows User_Data up to
  2^32 - 1 bytes; the size is now compared in `size_t`.
- F6 (spec `rj_content_size`): streaming decoding (`ZSTD_decompressContinue`) did not compare the decoded size with
  `Frame_Content_Size` when a frame ends with an empty last block; one-shot decoding always does. The check the
  non-empty last block has is added.
- F7 (spec `api_untouched_output`): the single-pass shortcut of `ZSTD_decompressStream` decoded into all of the
  output space (`oend - op`), and the sequence copies' over-writes went past the frame's content, after the
  `output.pos` it returns; it now gets exactly the frame's declared content size (the shortcut is taken only when
  the output space holds it).
- F8 (spec `api_reset`): `ZSTD_DCtx_reset` with `ZSTD_reset_session_and_parameters` ("Return a DCtx to clean
  state") kept the streaming buffers and the literal buffer of earlier frames; with frames that break the format,
  later decoding depended on them. The reset now releases the buffers and clears the literal buffer.

## Fixes F9 and F10 (`fixes3.py`, after `fixes2.py`)

Proof attempts on the short specs found two expressions undefined in CompCert's C semantics, reached by uses
`zstd.h` allows; `fixes3.py` removes them, each changed line marked with its F-number
([docs/fixes-F9-F12.md](../docs/fixes-F9-F12.md): the expressions, why they are undefined, the runs in CompCert's
interpreter, the diffs):

- F9 (specs `rj_any_stream`, `api_untouched_output`, `api_short_output`): `ZSTD_decompressStream` and one-shot
  decoding (`ZSTD_decompressMultiFrame`, `ZSTD_decompressFrame`) computed pointer differences on an empty buffer
  passed as NULL (`NULL - NULL`); such a buffer now gets a non-NULL base, the 1-byte static `ZSTD_emptyBuffer`,
  never read or written, and the positions are computed from it. An empty NULL buffer behaves as an empty non-NULL
  one (differential test: identical results).
- F10 (spec `res_free`): one-shot decoding on a context with an unfinished streaming frame left `previousDstEnd` in
  the caller's buffer, which a resumed stream compared after the caller freed it; one-shot decoding
  (`ZSTD_decompressMultiFrame`) now ends the streaming frame (`streamStage = zdss_init`).

## Fix F11 (`fixes4.py`, after `fixes3.py`)

- F11 (specs `rj_any_dict`, `api_reset`): `FSE_readNCount`'s zero-repeat loop also stops once
  `charnum >= maxSV1`, so `charnum` stays bounded; results unchanged (differential test, `docs/fixes-F9-F12.md`).

## Fix F12 (`fixes5.py`, after `fixes4.py`)

- F12 (spec `res_free`): `ZSTD_copyDDictParameters` no longer computes `NULL + 0` for a DDict made by
  `ZSTD_createDDict(NULL, 0)`; the end of an empty dictionary is its start (`docs/fixes-F9-F12.md`).

## The hook H1 (`lawhooks.py`, last)

H1: `ZSTD_createDCtx_advancedP`, `ZSTD_createDCtx_advanced` with its allocator (`ZSTD_customMem`) passed by
pointer. The `res_` specs count the decoder's memory through that allocator; the public function takes the struct
by value, which VST cannot call (`GP_NO_STRUCT_API` leaves it out). One added function, calling the same
`ZSTD_createDCtx_internal`; nothing else changes.
