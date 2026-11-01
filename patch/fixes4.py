#!/usr/bin/env python3
# Fix F11 (run at the tree root after fixes3.py; the replacement is asserted to match once).
#   F11 (laws rj_any_dict, api_reset): FSE_readNCount's zero-repeat loop now also stops once charnum >= maxSV1, so
#      charnum stays bounded and the function's existing too-many-symbols check applies (docs/fixes-F9-F12.md).
import sys


def edit(path, pairs):
    s = open(path).read()
    for old, new in pairs:
        n = s.count(old)
        assert n == 1, (path, old[:80], n)
        s = s.replace(old, new)
    open(path, 'w').write(s)


edit('lib/common/entropy_common.c', [
    ('            while (repeats >= 12) {\n',
     '            while (repeats >= 12 && charnum < maxSV1) {   /* F11: was (repeats >= 12) */\n'),
])
print('fixes4: 1 file patched (F11)', file=sys.stderr)
