#!/usr/bin/env python3
# Bug fixes F5-F8 found by the zstd short laws (run at the tree root after fixes.py; each replacement is asserted to
# match once).  Like fixes.py they change zstd's behaviour, only where it deviates from RFC 8878 or zstd.h:
#   F5 (skippable frames of 2^32 - 8 bytes of User_Data or more refused; laws rfc_skippable,
#      api_frame_size): readSkippableFrameSize refused Frame_Size values >= 2^32 - 8 (a 32-bit sum that would wrap),
#      though RFC 8878 3.1.2 allows User_Data up to 2^32 - 1 bytes; compare in size_t instead.
#   F6 (law rj_content_size): streaming decoding (ZSTD_decompressContinue) did not compare the decoded size
#      with Frame_Content_Size when the frame ends with an empty last block; one-shot decoding always does.
#   F7 (ZSTD_decompressStream writes past output.pos; law api_untouched_output): the single-pass
#      shortcut of ZSTD_decompressStream decoded into all of the output space (oend - op), and the sequence copies'
#      wildcopy over-writes went past the frame's content, after the output.pos it returns; give it exactly the frame's
#      declared content size (the shortcut is taken only when the output space holds it).
#   F8 (a context after ZSTD_DCtx_reset does not behave like a new one; law api_reset): resetting the
#      parameters ("Return a DCtx to clean state") kept the streaming buffers and the literal buffer of earlier frames;
#      with frames that break the format, later decoding depends on them (bytes of an earlier frame's literals in the
#      output, as with a match beyond the window; more output before an error).  Release the buffers and clear the literal buffer.
import sys


def edit(path, pairs):
    s = open(path).read()
    for old, new in pairs:
        n = s.count(old)
        assert n == 1, (path, old[:80], n)
        s = s.replace(old, new)
    open(path, 'w').write(s)


edit('lib/decompress/zstd_decompress.c', [
    # F5
    ('    RETURN_ERROR_IF((U32)(sizeU32 + ZSTD_SKIPPABLEHEADERSIZE) < sizeU32,\n'
     '                    frameParameter_unsupported, "");\n'
     '    {   size_t const skippableSize = skippableHeaderSize + sizeU32;\n'
     '        RETURN_ERROR_IF(skippableSize > srcSize, srcSize_wrong, "");\n'
     '        return skippableSize;\n'
     '    }\n',
     '    RETURN_ERROR_IF(sizeU32 > srcSize - skippableHeaderSize, srcSize_wrong, "");   /* F5: User_Data up to 2^32 - 1 bytes (RFC 8878 3.1.2); was a 32-bit sum, refusing >= 2^32 - 8 */\n'
     '    return skippableHeaderSize + sizeU32;\n'),
    # F6
    ('            /* empty block */\n'
     '            if (bp.lastBlock) {\n',
     '            /* empty block */\n'
     '            if (bp.lastBlock) {\n'
     '                RETURN_ERROR_IF(   /* F6: the end-of-frame check of a non-empty last block, below */\n'
     '                    dctx->fParams.frameContentSize != ZSTD_CONTENTSIZE_UNKNOWN\n'
     '                 && dctx->decodedSize != dctx->fParams.frameContentSize,\n'
     '                    corruption_detected, "");\n'),
    # F7
    ('                    size_t const decompressedSize = ZSTD_decompress_usingDDict(zds, op, (size_t)(oend-op), istart, cSize, ZSTD_getDDict(zds));\n',
     '                    size_t const decompressedSize = ZSTD_decompress_usingDDict(zds, op, (size_t)zds->fParams.frameContentSize, istart, cSize, ZSTD_getDDict(zds));   /* F7: was (size_t)(oend-op): no write past the frame\'s content */\n'),
    # F8
    ('        ZSTD_clearDict(dctx);\n'
     '        ZSTD_DCtx_resetParameters(dctx);\n'
     '    }\n'
     '    return 0;\n',
     '        ZSTD_clearDict(dctx);\n'
     '        ZSTD_DCtx_resetParameters(dctx);\n'
     '        if (!dctx->staticSize) {   /* F8: a clean state: no buffers or literals kept from earlier frames */\n'
     '            ZSTD_customFreeP(dctx->inBuff, &dctx->customMem);\n'
     '            dctx->inBuff = NULL;\n'
     '            dctx->inBuffSize = 0;\n'
     '            dctx->outBuffSize = 0;\n'
     '        }\n'
     '        dctx->oversizedDuration = 0;\n'
     '        ZSTD_memset(dctx->litExtraBuffer, 0, sizeof(dctx->litExtraBuffer));\n'
     '    }\n'
     '    return 0;\n'),
])
print('fixes2: 1 file patched (F5-F8)', file=sys.stderr)
