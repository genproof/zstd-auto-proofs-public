#!/usr/bin/env python3
# Conformance fixes F9 and F10 (run at the tree root after fixes2.py; each replacement is asserted to match once).  The
# short laws hold on the code only if no execution reaches an expression that CompCert's C semantics (the semantics
# of the theorems) leaves undefined; the proof attempts found such expressions, reached by uses that
# zstd.h allows.  Each edit changes no result of any execution that does not reach them (docs/fixes-F9-F12.md):
#   F9 (laws rj_any_stream, api_untouched_output, api_short_output): ZSTD_decompressStream with an empty buffer passed as NULL (zstd.h
#      allows NULL with size 0) computed iend - ip, oend - op, ip - input->src, op - output->dst on two NULL pointers,
#      undefined in ISO C (6.5.6p9) and in CompCert (Cop.sem_sub needs two pointers into one block).  An empty NULL
#      buffer now gets a non-NULL base, a 1-byte static object that is never read or written (every access through
#      it has size 0), so every pointer of the function points into one object; the positions are computed from
#      that base.  The output descriptor (ZSTD_checkOutBuffer, expectedOutBuffer) still holds the caller's NULL.
#      The same for one-shot decoding (law api_short_output): ZSTD_decompressMultiFrame and ZSTD_decompressFrame,
#      with dst NULL and capacity 0, computed oend - op, op - ostart and dst - dststart on NULL; dst gets the same
#      base there.  An empty NULL buffer now behaves exactly as an empty non-NULL one.
#   F10 (law res_free): one-shot decoding (ZSTD_decompressDCtx, ZSTD_decompress_usingDict(DDict), all through
#      ZSTD_decompressMultiFrame) on a context whose streaming frame was left unfinished set previousDstEnd to the
#      caller's dst and left the stream in its frame; the next ZSTD_decompressStream resumed it and compared its
#      output pointer with previousDstEnd (ZSTD_checkContinuity), a pointer into a buffer the caller may have freed
#      by then: undefined (CompCert: Val.cmplu_bool needs both pointers valid).  One-shot decoding now ends the
#      stream's frame (streamStage = zdss_init, as ZSTD_DCtx_reset(.., ZSTD_reset_session_only) does), so the next
#      ZSTD_decompressStream starts a new frame, whose ZSTD_decompressBegin clears previousDstEnd first.
import sys


def edit(path, pairs):
    s = open(path).read()
    for old, new in pairs:
        n = s.count(old)
        assert n == 1, (path, old[:80], n)
        s = s.replace(old, new)
    open(path, 'w').write(s)


edit('lib/decompress/zstd_decompress.c', [
    # F9
    ('size_t ZSTD_decompressStream(ZSTD_DStream* zds, ZSTD_outBuffer* output, ZSTD_inBuffer* input)\n'
     '{\n'
     '    const char* const src = (const char*)input->src;\n',
     'size_t ZSTD_decompressStream(ZSTD_DStream* zds, ZSTD_outBuffer* output, ZSTD_inBuffer* input)\n'
     '{\n'
     '    const char* const src = input->src != NULL ? (const char*)input->src : (const char*)ZSTD_emptyBuffer;   /* F9: was (const char*)input->src: no pointer difference on NULL */\n'),
    ('    char* const dst = (char*)output->dst;\n',
     '    char* const dst = output->dst != NULL ? (char*)output->dst : (char*)ZSTD_emptyBuffer;   /* F9: was (char*)output->dst */\n'),
    ('    input->pos = (size_t)(ip - (const char*)(input->src));\n'
     '    output->pos = (size_t)(op - (char*)(output->dst));\n',
     '    input->pos = (size_t)(ip - src);   /* F9: was (size_t)(ip - (const char*)(input->src)) */\n'
     '    output->pos = (size_t)(op - dst);   /* F9: was (size_t)(op - (char*)(output->dst)) */\n'),
    # F9, one-shot decoding (law api_short_output): dst NULL with capacity 0
    ('static\n'
     'ZSTD_ALLOW_POINTER_OVERFLOW_ATTR\n'
     'size_t ZSTD_decompressMultiFrame(ZSTD_DCtx* dctx,\n',
     '/* F9: the base of an empty buffer passed as NULL; never read or written (every access through it has size 0) */\n'
     'static const BYTE ZSTD_emptyBuffer[1] = { 0 };\n'
     '\n'
     'static\n'
     'ZSTD_ALLOW_POINTER_OVERFLOW_ATTR\n'
     'size_t ZSTD_decompressMultiFrame(ZSTD_DCtx* dctx,\n'),
    ('    void* const dststart = dst;\n'
     '    int moreThan1Frame = 0;\n',
     '    void* const dststart = dst != NULL ? dst : (void*)ZSTD_emptyBuffer;   /* F9: was dst: no pointer difference on NULL */\n'
     '    int moreThan1Frame = 0;\n'),
    # F10
    ('    DEBUGLOG(5, "ZSTD_decompressMultiFrame");\n',
     '    DEBUGLOG(5, "ZSTD_decompressMultiFrame");\n'
     '    dctx->streamStage = zdss_init;   /* F10: one-shot decoding ends a streaming frame left unfinished (its state, previousDstEnd included, is overwritten) */\n'
     '    dst = dststart;   /* F9 */\n'),
])
print('fixes3: 1 file patched (F9, F10)', file=sys.stderr)
