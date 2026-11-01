#!/usr/bin/env python3
# genproof idiom patch of zstd's decoder (run at the tree root; patch/GENPROOF-PATCH.md).  Each replacement
# is asserted to match exactly once, so the script fails loudly on an upstream change instead of patching
# the wrong place.  Every changed line carries a `genproof:` comment with the original.
import sys


def edit(path, pairs):
    s = open(path).read()
    for old, new in pairs:
        n = s.count(old)
        assert n == 1, (path, old[:80], n)
        s = s.replace(old, new)
    open(path, 'w').write(s)


# 1. ZSTD_decompressFrame: the in-place test orders pointers into src and dst, two different objects.
#    GP_INPLACE defaults to the original test; the verified configuration (genproof.conf) sets it to 0:
#    src and dst are separate objects, where the original test is always false.
edit('lib/decompress/zstd_decompress.c', [
    ('#include "zstd_decompress_block.h"   /* ZSTD_decompressBlock_internal */\n',
     '#include "zstd_decompress_block.h"   /* ZSTD_decompressBlock_internal */\n'
     '#ifndef GP_INPLACE   /* genproof: the in-place test, see ZSTD_decompressFrame */\n'
     '#define GP_INPLACE(ip, op, oend) ((ip) >= (op) && (ip) < (oend))\n'
     '#endif\n'),
    ('        if (ip >= op && ip < oBlockEnd) {',
     '        if (GP_INPLACE(ip, op, oBlockEnd)) {  /* genproof: was ip >= op && ip < oBlockEnd */'),
    # 2. ZSTD_refDictContent: previousDstEnd - prefixStart is NULL - NULL on a fresh context.
    ('    dctx->virtualStart = (const char*)dict - ((const char*)(dctx->previousDstEnd) - (const char*)(dctx->prefixStart));',
     '    dctx->virtualStart = (const char*)dict - (dctx->previousDstEnd == NULL ? 0 : ((const char*)(dctx->previousDstEnd) - (const char*)(dctx->prefixStart)));  /* genproof: was dict - (previousDstEnd - prefixStart): NULL - NULL on a fresh context */'),
])

edit('lib/decompress/zstd_decompress_block.c', [
    # 3. ZSTD_decompressBlock_internal: an address-range test on (size_t)dst.  Implementation-defined in
    #    ISO C, undefined in CompCert (a cast pointer stays a pointer).  GP_DST_NEAR_TOP defaults to the
    #    original; genproof.conf sets it to 0 (no object lies in the top MiB of CompCert's offsets).
    ('#include "zstd_decompress_block.h"\n',
     '#include "zstd_decompress_block.h"\n'
     '#ifndef GP_DST_NEAR_TOP   /* genproof: the address-range test, see ZSTD_decompressBlock_internal */\n'
     '#define GP_DST_NEAR_TOP(dst) (MEM_64bits() && sizeof(size_t) == sizeof(void*) && (size_t)(-1) - (size_t)(dst) < (size_t)(1 << 20))\n'
     '#endif\n'),
    ('        RETURN_ERROR_IF(MEM_64bits() && sizeof(size_t) == sizeof(void*) && (size_t)(-1) - (size_t)dst < (size_t)(1 << 20), dstSize_tooSmall,',
     '        RETURN_ERROR_IF(GP_DST_NEAR_TOP(dst), dstSize_tooSmall,  /* genproof: was MEM_64bits() && sizeof(size_t) == sizeof(void*) && (size_t)(-1) - (size_t)dst < (size_t)(1 << 20) */'),
    # 4. ZSTD_checkContinuity: the same NULL - NULL as 2, on the first block of a fresh context.
    ('        dctx->virtualStart = (const char*)dst - ((const char*)(dctx->previousDstEnd) - (const char*)(dctx->prefixStart));',
     '        dctx->virtualStart = (const char*)dst - (dctx->previousDstEnd == NULL ? 0 : ((const char*)(dctx->previousDstEnd) - (const char*)(dctx->prefixStart)));  /* genproof: was dst - (previousDstEnd - prefixStart): NULL - NULL on the first call */'),
    # 5. ZSTD_safecopy: op - ip up front, although op (dst) and ip (literals) are different objects
    #    unless ovtype says they overlap.  Computed only where it is used.
    ('    ptrdiff_t const diff = op - ip;\n'
     '    BYTE* const oend = op + length;\n'
     '\n'
     '    assert((ovtype == ZSTD_no_overlap && (diff <= -8 || diff >= 8 || op >= oend_w)) ||\n'
     '           (ovtype == ZSTD_overlap_src_before_dst && diff >= 0));\n',
     '    BYTE* const oend = op + length;\n'
     '    /* genproof: was `ptrdiff_t const diff = op - ip;` up front (and an assert on it): op and ip are\n'
     '     * different objects unless ovtype == ZSTD_overlap_src_before_dst */\n'),
    ('        assert(diff > 0);\n'
     '        ZSTD_overlapCopy8(&op, &ip, (size_t)diff);',
     '        ZSTD_overlapCopy8(&op, &ip, (size_t)(op - ip));  /* genproof: was (size_t)diff */'),
])

# 6. ZSTD_execSequence and ZSTD_execSequenceSplitLitBuffer: iLitEnd = *litPtr + litLength and
#    oMatchEnd = op + sequenceLength are formed before they are checked, and compared: past the end of
#    the literals or of dst when the sequence does not fit (any dst that is too small).  The same tests
#    on distances inside the objects.
edit('lib/decompress/zstd_decompress_block.c', [
    ('        iLitEnd > litLimit ||\n'
     '        oMatchEnd > oend_w ||\n',
     '        litLimit - *litPtr < (ptrdiff_t)sequence.litLength ||  /* genproof: was iLitEnd > litLimit */\n'
     '        oend_w - op < (ptrdiff_t)sequenceLength ||  /* genproof: was oMatchEnd > oend_w (oMatchEnd may lie past the end of dst) */\n'),
    ('            iLitEnd > litLimit ||\n'
     '            oMatchEnd > oend_w ||\n',
     '            litLimit - *litPtr < (ptrdiff_t)sequence.litLength ||  /* genproof: was iLitEnd > litLimit */\n'
     '            oend_w - op < (ptrdiff_t)sequenceLength ||  /* genproof: was oMatchEnd > oend_w (oMatchEnd may lie past the end of dst) */\n'),
])

# 7. ZSTD_wildcopy: dst - src up front, the same as 5.
edit('lib/common/zstd_internal.h', [
    ('    ptrdiff_t diff = (BYTE*)dst - (const BYTE*)src;\n'
     '    const BYTE* ip = (const BYTE*)src;\n'
     '    BYTE* op = (BYTE*)dst;\n'
     '    BYTE* const oend = op + length;\n'
     '\n'
     '    if (ovtype == ZSTD_overlap_src_before_dst && diff < WILDCOPY_VECLEN) {',
     '    const BYTE* ip = (const BYTE*)src;\n'
     '    BYTE* op = (BYTE*)dst;\n'
     '    BYTE* const oend = op + length;\n'
     '\n'
     '    /* genproof: was `ptrdiff_t diff = dst - src;` up front: src and dst are different objects unless ovtype says they overlap */\n'
     '    if (ovtype == ZSTD_overlap_src_before_dst && (BYTE*)dst - (const BYTE*)src < WILDCOPY_VECLEN) {'),
    ('        assert(diff >= WILDCOPY_VECLEN || diff <= -WILDCOPY_VECLEN);\n', ''),
])

# 8. BIT_reloadDStream(Fast): limitPtr = start + sizeof(bitContainer) lies past the end of a bitstream
#    shorter than 8 bytes at the end of the input; compare the distance from start instead.
edit('lib/common/bitstream.h', [
    ('    if (UNLIKELY(bitD->ptr < bitD->limitPtr))',
     '    if (UNLIKELY((size_t)(bitD->ptr - bitD->start) < sizeof(bitD->bitContainer)))  /* genproof: was bitD->ptr < bitD->limitPtr (limitPtr = start + 8 lies past a short stream) */'),
    ('    if (bitD->ptr >= bitD->limitPtr) {',
     '    if ((size_t)(bitD->ptr - bitD->start) >= sizeof(bitD->bitContainer)) {  /* genproof: was bitD->ptr >= bitD->limitPtr */'),
])

# 9. XXH64_update (the frame checksum; XXH32 is not used by the decoder): `p + 32 <= bEnd` forms a pointer past the
#    end (or before the start) of the input when fewer bytes remain; found by the constructive laws.
edit('lib/common/xxhash.h', [
    ('        if (p+32 <= bEnd) {',
     '        if ((size_t)(bEnd - p) >= 32) {  /* genproof: was p+32 <= bEnd */'),
])

# 10. ZSTD_decompressBlock_internal: totalHistorySize = dst + blockSizeMax - virtualStart is computed for every compressed
#     block, but virtualStart is still the NULL of ZSTD_decompressBegin when the output capacity is 0
#     (ZSTD_checkContinuity sets it only for a non-empty dst): dst - NULL.  The value is dead then (it is used on
#     32-bit only, or after the dstCapacity == 0 && nbSeq > 0 error).  Found while proving.
edit('lib/decompress/zstd_decompress_block.c', [
    ('        size_t const totalHistorySize = ZSTD_totalHistorySize(ZSTD_maybeNullPtrAdd(dst, (ptrdiff_t)blockSizeMax), (BYTE const*)dctx->virtualStart);',
     '        size_t const totalHistorySize = dstCapacity == 0 ? 0 :   /* genproof: was computed unconditionally: dst - NULL while virtualStart is NULL (capacity 0) */\n'
     '            ZSTD_totalHistorySize(ZSTD_maybeNullPtrAdd(dst, (ptrdiff_t)blockSizeMax), (BYTE const*)dctx->virtualStart);'),
])

# 11. ZSTD_safecopy and ZSTD_safecopyDstBeforeSrc (the copies near the end of the output): the limit oend_w =
#     oend - WILDCOPY_OVERLENGTH lies before the output when it is shorter than 32 bytes, and is compared with
#     pointers into it.  Compare distances within the output instead (found by the interpreter on frame_sequences).
edit('lib/decompress/zstd_decompress_block.c', [
    ('    if (oend <= oend_w) {\n',
     '    if (oend_w - oend >= 0) {  /* genproof: was oend <= oend_w */\n'),
    ('    if (op <= oend_w) {\n',
     '    if (oend_w - op >= 0) {  /* genproof: was op <= oend_w */\n'),
    ('    if (op <= oend - WILDCOPY_OVERLENGTH && diff < -WILDCOPY_VECLEN) {',
     '    if (oend - op >= WILDCOPY_OVERLENGTH && diff < -WILDCOPY_VECLEN) {  /* genproof: was op <= oend - WILDCOPY_OVERLENGTH */'),
])

# 12. BIT_reloadDStream, the cautious update: `ptr - nbBytes < start` forms a pointer up to 7 bytes before the start
#     of the bitstream; when the stream begins near the start of its buffer (streaming: the block body at offset 0 of
#     inBuff or of an input chunk), that is before the object.  Compare the distance instead.  Found while
#     proving; the interpreter cannot see it, as ccomp's malloc keeps 8 header bytes before each block.
edit('lib/common/bitstream.h', [
    ('        if (bitD->ptr - nbBytes < bitD->start) {',
     '        if ((size_t)(bitD->ptr - bitD->start) < nbBytes) {  /* genproof: was bitD->ptr - nbBytes < bitD->start */'),
])

# 13. The four sequence executors, extDict branch: `match + sequence.matchLength <= dictEnd` forms a pointer past the
#     end of the dictionary's object when a match starts in the dictionary and runs on into dst (zstd's compressor
#     makes such frames).  ZSTD_loadDEntropy: `dictPtr+12 > dictEnd`, past the dictionary when a formatted dictionary
#     lacks its 12 repeat-offset bytes.  The same tests on signed distances inside the objects, as in 6.  Found while
#     proving (ASan pointer-compare reports both).
p13 = 'lib/decompress/zstd_decompress_block.c'
s13 = open(p13).read()
old = '        if (match + sequence.matchLength <= dictEnd) {\n'
assert s13.count(old) == 4, s13.count(old)
s13 = s13.replace(old, '        if (dictEnd - match >= (ptrdiff_t)sequence.matchLength) {   /* genproof: was match + sequence.matchLength <= dictEnd (past the dictionary when the match runs into dst) */\n')
open(p13, 'w').write(s13)
p13 = 'lib/decompress/zstd_decompress.c'
s13 = open(p13).read()
old = '    RETURN_ERROR_IF(dictPtr+12 > dictEnd, dictionary_corrupted, "");\n'
assert s13.count(old) == 1, s13.count(old)
s13 = s13.replace(old, '    RETURN_ERROR_IF(dictEnd - dictPtr < 12, dictionary_corrupted, "");   /* genproof: was dictPtr+12 > dictEnd */\n')
open(p13, 'w').write(s13)

# 14. ZSTD_decodeSeqHeaders: `ip+2 > iend` (nbSeq byte 0xFF) and `ip+1 > iend` form pointers past the end of the input
#     when the input ends inside or right after the nbSeq field (0 or 1 byte after 0xFF; ip == iend after the field).
#     The same tests on the distance `iend - ip` (ip <= iend always holds at both).  Found while proving
#     (ASan pointer-compare reports both).
p14 = 'lib/decompress/zstd_decompress_block.c'
s14 = open(p14).read()
for old, new in (('            RETURN_ERROR_IF(ip+2 > iend, srcSize_wrong, "");\n',
                  '            RETURN_ERROR_IF(iend - ip < 2, srcSize_wrong, "");   /* genproof: was ip+2 > iend */\n'),
                 ('    RETURN_ERROR_IF(ip+1 > iend, srcSize_wrong, ""); /* minimum possible size: 1 byte for symbol encoding types */\n',
                  '    RETURN_ERROR_IF(iend - ip < 1, srcSize_wrong, ""); /* minimum possible size: 1 byte for symbol encoding types */   /* genproof: was ip+1 > iend */\n')):
    assert s14.count(old) == 1, (old, s14.count(old))
    s14 = s14.replace(old, new)
open(p14, 'w').write(s14)

# 15. FSE_readNCount_body: `ip + (bitCount>>3) <= iend-4` (after a count, and after a run of zero counts) forms a
#     pointer past the end of the table description when it ends its object and the reader is clamped to its last
#     4 bytes (a count of up to 16 bits takes bitCount to 47: ip + 5 = iend + 1; reachable only after a count, the
#     run of zeros keeps bitCount <= 34).  The same test on the distance `(iend-4) - ip` (iend-4 is inside the
#     object: hbSize >= 8), at both sites.  Found while proving (ASan
#     pointer-compare reports it).
p15 = 'lib/common/entropy_common.c'
s15 = open(p15).read()
old = '            if (LIKELY(ip <= iend-7) || (ip + (bitCount>>3) <= iend-4)) {\n'
assert s15.count(old) == 2, s15.count(old)
s15 = s15.replace(old, '            if (LIKELY(ip <= iend-7) || ((bitCount>>3) <= (iend-4) - ip)) {   /* genproof: was ip + (bitCount>>3) <= iend-4 */\n')
open(p15, 'w').write(s15)

# 16. Split literals: `litPtr + sequence.litLength > dctx->litBufferEnd` (ZSTD_decompressSequences_bodySplitLitBuffer)
#     and twice in ZSTD_decompressSequencesLong_body: litPtr is in dst (the head of the split literals), litLength comes
#     from the bitstream (up to 131071), so the sum can lie far past dst's object.  The same tests on the distance
#     `litBufferEnd - litPtr` (litPtr <= litBufferEnd whenever the literals are split: litPtr only advances past a
#     passed test).  Found while proving (ASan pointer-compare reports it).
p16 = 'lib/decompress/zstd_decompress_block.c'
s16 = open(p16).read()
for old, new in (('                if (litPtr + sequence.litLength > dctx->litBufferEnd) break;\n',
                  '                if ((size_t)(dctx->litBufferEnd - litPtr) < sequence.litLength) break;   /* genproof: was litPtr + sequence.litLength > dctx->litBufferEnd */\n'),
                 ('            if (dctx->litBufferLocation == ZSTD_split && litPtr + sequences[(seqNb - ADVANCED_SEQS) & STORED_SEQS_MASK].litLength > dctx->litBufferEnd) {\n',
                  '            if (dctx->litBufferLocation == ZSTD_split && (size_t)(dctx->litBufferEnd - litPtr) < sequences[(seqNb - ADVANCED_SEQS) & STORED_SEQS_MASK].litLength) {   /* genproof: was litPtr + ...litLength > dctx->litBufferEnd */\n'),
                 ('            if (dctx->litBufferLocation == ZSTD_split && litPtr + sequence->litLength > dctx->litBufferEnd) {\n',
                  '            if (dctx->litBufferLocation == ZSTD_split && (size_t)(dctx->litBufferEnd - litPtr) < sequence->litLength) {   /* genproof: was litPtr + sequence->litLength > dctx->litBufferEnd */\n')):
    assert s16.count(old) == 1, (old, s16.count(old))
    s16 = s16.replace(old, new)
open(p16, 'w').write(s16)

# 17. Zeroed decoder memory: the context (ZSTD_createDCtx_internal) and the streaming buffers (ZSTD_decompressStream)
#     come from ZSTD_customCalloc instead of ZSTD_customMalloc.  The decoder reads bytes it never wrote: ZSTD_copy16 /
#     the wildcopies copy up to 32 bytes past a sequence's literals (from litExtraBuffer, inside the context) into the
#     output's slack, and in buffered streaming, after the ring buffer wraps, a match into the extDict window (the
#     same ring) can copy that slack into the regenerated content, which the frame checksum then hashes: arithmetic
#     on never-written bytes, undefined in CompCert's semantics (spec x_any_stream).  Not undefined in ISO C (malloc'd bytes are indeterminate, and unsigned char
#     and uint32_t have no trap representations): an implementation inconsistency.  Zeroed memory
#     gives the same results on every frame that reads no never-written byte; on the others those bytes are 0.
p17 = 'lib/decompress/zstd_decompress.c'
s17 = open(p17).read()
for old, new in (('    {   ZSTD_DCtx* const dctx = (ZSTD_DCtx*)ZSTD_customMalloc(sizeof(*dctx), customMem);\n',
                  '    {   ZSTD_DCtx* const dctx = (ZSTD_DCtx*)ZSTD_customCalloc(sizeof(*dctx), customMem);   /* genproof: was ZSTD_customMalloc (zeroed, patch item 17) */\n'),
                 ('                            zds->inBuff = (char*)ZSTD_customMalloc(bufferSize, zds->customMem);\n',
                  '                            zds->inBuff = (char*)ZSTD_customCalloc(bufferSize, zds->customMem);   /* genproof: was ZSTD_customMalloc (zeroed, patch item 17) */\n')):
    assert s17.count(old) == 1, (old, s17.count(old))
    s17 = s17.replace(old, new)
open(p17, 'w').write(s17)

# 18. ZSTD_decodeLiteralsBlock, compressed literals split between dst and the context: after the Huffman decode into
#     dst, the last ZSTD_LITBUFFEREXTRASIZE decoded bytes are copied into dctx->litExtraBuffer BEFORE the error check, so
#     a failed decode fills the context's buffer with bytes of dst it never wrote, undoing item 17 for any later use of
#     the context (a stream after a failed one-shot decode: the item-17 path again).  The copy only after a successful
#     decode: on success nothing changes; on an error the same error, dst as before (the memmove in dst still runs), and
#     litExtraBuffer keeps its previous bytes.  Found while proving.
p18 = 'lib/decompress/zstd_decompress_block.c'
s18 = open(p18).read()
old18 = '                    ZSTD_memcpy(dctx->litExtraBuffer, dctx->litBufferEnd - ZSTD_LITBUFFEREXTRASIZE, ZSTD_LITBUFFEREXTRASIZE);\n'
assert s18.count(old18) == 1, s18.count(old18)
s18 = s18.replace(old18, '                    if (!HUF_isError(hufSuccess))   /* genproof: the copy only after a successful decode (patch item 18) */\n    '
                  + old18)
open(p18, 'w').write(s18)


# 19. ZSTD_allocateLiteralsBuffer: when the literals go into dst (the whole literal buffer after the block's output, or
#     the head of a split one at the end of the block's output when the literals are copied or set at once), the
#     WILDCOPY_OVERLENGTH bytes after them are zeroed.  ZSTD_copy16 and the wildcopies of the sequence executors read up
#     to 16 bytes past a sequence's literals, so with the literals at the end of the buffer they read bytes of dst that
#     nothing wrote.  ISO C allows that through memcpy/memmove, but the memcpy and memmove of QuickProof's libc
#     (libc/libc.c, v0.1.0-beta.1) copy through unsigned char, which CompCert's semantics cannot do with a byte that was
#     never written: the copy is stuck (seen natively with MemorySanitizer on laws any_stream and any_params: the
#     single-pass shortcut of ZSTD_decompressStream into the caller's buffer).  zstd up to v1.4.x zeroed the same
#     bytes (`memset(dctx->litBuffer + dctx->litSize, 0, WILDCOPY_OVERLENGTH)`).  Results are the same: the zeroed bytes
#     lie past the block's literals and are only ever over-read; in dst they lie beyond the block's output or are
#     overwritten by it.  The literal buffer in the context needs nothing (item 17), nor do literals read in place from
#     the input, nor the Huffman-decoded split buffer (after the shift below, its slack holds decoded bytes).
p19 = 'lib/decompress/zstd_decompress_block.c'
s19 = open(p19).read()
for old, new in ((
        '        dctx->litBuffer = (BYTE*)dst + blockSizeMax + WILDCOPY_OVERLENGTH;\n'
        '        dctx->litBufferEnd = dctx->litBuffer + litSize;\n'
        '        dctx->litBufferLocation = ZSTD_in_dst;\n',
        '        dctx->litBuffer = (BYTE*)dst + blockSizeMax + WILDCOPY_OVERLENGTH;\n'
        '        dctx->litBufferEnd = dctx->litBuffer + litSize;\n'
        '        dctx->litBufferLocation = ZSTD_in_dst;\n'
        '        ZSTD_memset(dctx->litBufferEnd, 0, WILDCOPY_OVERLENGTH);   /* genproof: the slack the literal copies over-read is written (patch item 19) */\n'),
        ('            dctx->litBufferEnd = dctx->litBuffer + litSize - ZSTD_LITBUFFEREXTRASIZE;\n',
         '            dctx->litBufferEnd = dctx->litBuffer + litSize - ZSTD_LITBUFFEREXTRASIZE;\n'
         '            ZSTD_memset(dctx->litBufferEnd, 0, WILDCOPY_OVERLENGTH);   /* genproof: the slack the literal copies over-read is written (patch item 19) */\n')):
    assert s19.count(old) == 1, (old, s19.count(old))
    s19 = s19.replace(old, new)
open(p19, 'w').write(s19)

# 20. ZSTD_decodeLiteralsBlock, compressed literals split between dst and the context: the shift of the dst part
#     (ZSTD_memmove) ran before the Huffman error check too, so after a failed decode it moved bytes of dst that the
#     decode never wrote: stuck in CompCert's semantics with QuickProof's byte-loop memmove (item 19).  Like the copy of
#     item 18, the shift now runs only after a successful decode.  On success nothing changes; on an error the same
#     error code, and dst keeps the bytes the decode left (dst is unspecified after an error).
p20 = 'lib/decompress/zstd_decompress_block.c'
s20 = open(p20).read()
old20 = ('                    if (!HUF_isError(hufSuccess))   /* genproof: the copy only after a successful decode (patch item 18) */\n'
         '                        ZSTD_memcpy(dctx->litExtraBuffer, dctx->litBufferEnd - ZSTD_LITBUFFEREXTRASIZE, ZSTD_LITBUFFEREXTRASIZE);\n'
         '                    ZSTD_memmove(dctx->litBuffer + ZSTD_LITBUFFEREXTRASIZE - WILDCOPY_OVERLENGTH, dctx->litBuffer, litSize - ZSTD_LITBUFFEREXTRASIZE);\n')
new20 = ('                    if (!HUF_isError(hufSuccess))   /* genproof: the copy only after a successful decode (patch item 18) */\n'
         '                        ZSTD_memcpy(dctx->litExtraBuffer, dctx->litBufferEnd - ZSTD_LITBUFFEREXTRASIZE, ZSTD_LITBUFFEREXTRASIZE);\n'
         '                    if (!HUF_isError(hufSuccess))   /* genproof: the shift only after a successful decode (patch item 20) */\n'
         '                        ZSTD_memmove(dctx->litBuffer + ZSTD_LITBUFFEREXTRASIZE - WILDCOPY_OVERLENGTH, dctx->litBuffer, litSize - ZSTD_LITBUFFEREXTRASIZE);\n')
assert s20.count(old20) == 1, s20.count(old20)
s20 = s20.replace(old20, new20)
open(p20, 'w').write(s20)

print('zstdpatch: 7 files patched', file=sys.stderr)
