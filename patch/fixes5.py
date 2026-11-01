#!/usr/bin/env python3
# Fix F12 (run at the tree root after fixes4.py; the replacement is asserted to match once).
#   F12 (law res_free): ZSTD_createDDict(NULL, 0) is accepted (zstd_ddict.c: dictContent = dict, dictSize = 0), and
#      decoding with that DDict computed dictContent + dictSize, i.e. NULL + 0 (undefined in ISO C, 6.5.6p8). The end
#      pointer is now the start itself when the size is 0: the same value in every execution (docs/fixes-F9-F12.md).
import sys


def edit(path, pairs):
    s = open(path).read()
    for old, new in pairs:
        n = s.count(old)
        assert n == 1, (path, old[:80], n)
        s = s.replace(old, new)
    open(path, 'w').write(s)


edit('lib/decompress/zstd_ddict.c', [
    ('    dctx->dictEnd = (const BYTE*)ddict->dictContent + ddict->dictSize;\n',
     '    dctx->dictEnd = ddict->dictSize != 0 ? (const BYTE*)ddict->dictContent + ddict->dictSize\n'
     '                                         : (const BYTE*)ddict->dictContent;   /* F12: was dictContent + dictSize (NULL + 0) */\n'),
])
print('fixes5: 1 file patched (F12)', file=sys.stderr)
