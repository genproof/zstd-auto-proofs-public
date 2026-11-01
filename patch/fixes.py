#!/usr/bin/env python3
# Changes F1-F4 of the verified configuration (run at the tree root after vstpatch.py; patch/GENPROOF-PATCH.md).
# Unlike zstdpatch.py and vstpatch.py, these change zstd's behaviour: each makes the code follow zstd.h in one case
# that a spec needs.  Each replacement is asserted to match once.
import sys


def edit(path, pairs):
    s = open(path).read()
    for old, new in pairs:
        n = s.count(old)
        assert n == 1, (path, old[:80], n)
        s = s.replace(old, new)
    open(path, 'w').write(s)


edit('lib/decompress/zstd_decompress.c', [
    # F1: "Provides the dictID required to decompressed the frame ... If @return == 0 ... This is not a
    # Zstandard frame."  Since a2ff6ea78 a skippable frame's header reports its magic variant in dictID.
    ('    if (ZSTD_isError(hError)) return 0;\n    return zfp.dictID;\n',
     '    if (ZSTD_isError(hError)) return 0;\n'
     '    if (zfp.frameType == ZSTD_skippableFrame) return 0;   /* genproof F1: not a Zstandard frame (dictID holds the magic variant) */\n'
     '    return zfp.dictID;\n'),
    # F2: the hint "will never request more than the remaining content of the compressed frame".  While the
    # magic number is incomplete the frame may be an empty skippable frame (8 bytes, the shortest frame); a skippable
    # frame's header is followed by no block header.
    ('                        return (MAX((size_t)ZSTD_FRAMEHEADERSIZE_MIN(zds->format), hSize) - zds->lhSize) + ZSTD_blockHeaderSize;   /* remaining header bytes + next block header */\n',
     '                        if (zds->format == ZSTD_f_zstd1 && (zds->lhSize < ZSTD_FRAMEIDSIZE || ZSTD_isSkippableFrame(zds->headerBuffer, zds->lhSize)))\n'
     '                            return (zds->lhSize < ZSTD_FRAMEIDSIZE ? (size_t)ZSTD_SKIPPABLEHEADERSIZE : hSize) - zds->lhSize;   /* genproof F2: frame type unknown (the shortest frame is an empty skippable one) or skippable: no block header follows */\n'
     '                        return (MAX((size_t)ZSTD_FRAMEHEADERSIZE_MIN(zds->format), hSize) - zds->lhSize) + ZSTD_blockHeaderSize;   /* remaining header bytes + next block header */\n'),
    # F3: the single-pass shortcut parses the input from this call's start (istart) as a frame; when the
    # header was partly loaded by an earlier call, istart is mid-frame, and bytes there that read as a frame are
    # "decoded" instead (a valid frame reported complete without its content).  Take it only when the whole header
    # was read in this call, i.e. istart is the frame's start.
    ('                && (U64)(size_t)(oend-op) >= zds->fParams.frameContentSize) {\n',
     '                && (U64)(size_t)(oend-op) >= zds->fParams.frameContentSize\n'
     '                && zds->lhSize == (size_t)(ip - istart)) {   /* genproof F3: istart is the frame start only if the whole header came in this call */\n'),
    # F4: ZSTD_d_refMultipleDDicts: "At decompression time, the appropriate dictID is selected from the set
    # of DDicts based on the dictID in the frame."  One-shot decoding loaded the DDict referenced last and only then
    # selected the frame's (ZSTD_decodeFrameHeader -> ZSTD_DCtx_selectFrameDDict), without loading it.  Select it
    # before loading, with the lookup streaming uses (zdss_loadHeader): the frame's DDict when the set has one.
    ('            /* we were called from ZSTD_decompress_usingDDict */\n'
     '            FORWARD_IF_ERROR(ZSTD_decompressBegin_usingDDict(dctx, ddict), "");\n',
     '            /* we were called from ZSTD_decompress_usingDDict */\n'
     '            if (dctx->refMultipleDDicts == ZSTD_rmd_refMultipleDDicts && dctx->ddictSet) {   /* genproof F4: load the frame\'s DDict, as streaming does */\n'
     '                ZSTD_FrameHeader zfh;\n'
     '                if (ZSTD_getFrameHeader_advanced(&zfh, src, srcSize, dctx->format) == 0) {\n'
     '                    const ZSTD_DDict* const frameDDict = ZSTD_DDictHashSet_getDDict(dctx->ddictSet, zfh.dictID);\n'
     '                    if (frameDDict) ddict = frameDDict;\n'
     '                }\n'
     '            }\n'
     '            FORWARD_IF_ERROR(ZSTD_decompressBegin_usingDDict(dctx, ddict), "");\n'),
])
print('fixes: 1 file patched (F1-F4)', file=sys.stderr)
