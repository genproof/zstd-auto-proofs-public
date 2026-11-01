#!/usr/bin/env python3
# The zstd short laws' one addition to the decoder (run at the tree root, after the other patch layers if any):
# ZSTD_createDCtx_advancedP, ZSTD_createDCtx_advanced with its allocator (ZSTD_customMem) passed by pointer.  The res_*
# laws count the decoder's memory through that allocator, as zlib's laws count it through zalloc/zfree; the public
# function takes the struct by value, which VST cannot call (this configuration leaves it out: GP_NO_STRUCT_API).
# Works on upstream (ZSTD_createDCtx_internal takes the struct by value) and on the VST layer (by pointer).
import sys

path = 'lib/decompress/zstd_decompress.c'
s = open(path).read()
anchor = 'ZSTD_DCtx* ZSTD_createDCtx(void)\n{\n'
assert s.count(anchor) == 1, anchor
byptr = 'static ZSTD_DCtx* ZSTD_createDCtx_internal(const ZSTD_customMem* customMem)' in s
arg = 'customMem' if byptr else '*customMem'
hook = ('/* quickproof laws (res_*): ZSTD_createDCtx_advanced with the allocator by pointer */\n'
        'ZSTD_DCtx* ZSTD_createDCtx_advancedP(const ZSTD_customMem* customMem);\n'
        'ZSTD_DCtx* ZSTD_createDCtx_advancedP(const ZSTD_customMem* customMem)\n'
        '{\n    return ZSTD_createDCtx_internal(%s);\n}\n\n' % arg)
s = s.replace(anchor, hook + anchor)
open(path, 'w').write(s)
print('lawhooks: ZSTD_createDCtx_advancedP added (%s)' % ('VST layer' if byptr else 'upstream'), file=sys.stderr)
