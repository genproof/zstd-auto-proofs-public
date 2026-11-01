#!/usr/bin/env python3
# genproof VST layer of the zstd decoder patch (run at the tree root after zstdpatch.py; patch/GENPROOF-PATCH.md).
# VST has no rule for assigning a struct ("Verifiable C does not support assignment to variables of struct or
# union type"), and clightgen without -fstruct-passing rejects struct parameters and returns.  So:
#   - every struct copy becomes a field-by-field copy (one small helper per type);
#   - every by-value struct parameter becomes a pointer to const; a callee that modifies its copy (seq_t in
#     ZSTD_execSequence*) takes a field-by-field local copy first, so by-value semantics are kept;
#   - every struct return becomes an out-pointer;
#   - public functions with a struct parameter or return (ZSTD_createDCtx_advanced, ZSTD_createDStream_advanced,
#     ZSTD_createDDict_advanced, ZSTD_dParam_getBounds) keep their API on top of a pointer version, and are left
#     out when GP_NO_STRUCT_API is defined (genproof.conf); so are the by-value allocation helpers, which the
#     compressor still uses;
#   - MEM_write64 as byte stores and BIT_initDStream's switch on an unsigned (below: VST cannot give the bytes of
#     a stored U64, and its switch rule takes only an int scrutinee).
# Only what VST needs: edits in functions that no law reaches (Spec_dead) are left out, except where clightgen
# cannot translate the file otherwise (struct parameters and returns).
# Each replacement is asserted to match the expected number of times.  Every changed place has a `genproof:` comment.
import re
import sys


def load(path):
    return open(path).read()


def save(path, s):
    open(path, 'w').write(s)


def rep(s, old, new, cnt=1):
    n = s.count(old)
    assert n == cnt, (old[:90], n, cnt)
    return s.replace(old, new)


def resub(s, pat, repl, cnt):
    s2, n = re.subn(pat, repl, s)
    assert n == cnt, (pat[:90], n, cnt)
    return s2


def split_args(text, start):
    """text[start] == '(': the argument strings of the call and the index after its ')'."""
    depth, args, cur, i = 0, [], start + 1, start
    while True:
        c = text[i]
        if c in '([':
            depth += 1
        elif c in ')]':
            depth -= 1
            if depth == 0:
                args.append(text[cur:i])
                return args, i + 1
        elif c == ',' and depth == 1:
            args.append(text[cur:i])
            cur = i + 1
        i += 1


def comment_spans(s):
    return [(m.start(), m.end()) for m in re.finditer(r'/\*.*?\*/|//[^\n]*', s, re.S)]


def by_pointer(s, fname, k, cnt):
    """Every call fname(...) (not the definition, not in a comment): argument k (a seq_t lvalue) passed by address."""
    out, pos, n = [], 0, 0
    spans = comment_spans(s)
    for m in re.finditer(r'\b%s\(' % re.escape(fname), s):
        if m.start() < pos or any(a <= m.start() < b for a, b in spans):
            continue
        before = s[max(0, m.start() - 30):m.start()]
        if re.search(r'size_t\s*$', before):      # the definition
            continue
        args, end = split_args(s, m.end() - 1)
        a = args[k].strip()
        args[k] = ' ' + (a[1:] if a.startswith('*') else '&' + a)
        if k == 0:
            args[k] = args[k].lstrip()
        out.append(s[pos:m.end() - 1] + '(' + ','.join(args) + ')')
        pos = end
        n += 1
    assert n == cnt, (fname, n, cnt)
    return ''.join(out) + s[pos:]


# ---------------------------------------------------------------------------------------------------------
# common/allocations.h: the allocation helpers by pointer, a ZSTD_customMem copy; by-value ones kept for the
# compressor, out of the verified configuration.
p = 'lib/common/allocations.h'
s = load(p)
a = s.index('MEM_STATIC void* ZSTD_customMalloc(size_t size, ZSTD_customMem customMem)')
b = s.index('#endif /* ZSTD_ALLOCATIONS_H */')
byval = s[a:b]
byptr = byval.replace('ZSTD_customMem customMem', 'const ZSTD_customMem* customMem').replace('customMem.', 'customMem->')
for f in ('ZSTD_customMalloc', 'ZSTD_customCalloc', 'ZSTD_customFree'):
    byptr = rep(byptr, f + '(', f + 'P(')
s = s[:a] + ('#ifndef GP_NO_STRUCT_API   /* genproof: struct parameters (the compressor uses these) */\n' + byval.rstrip() +
             '\n#endif\n\n/* genproof: the same helpers taking the allocator by pointer (VST: no struct parameters) */\n' +
             byptr.rstrip() + '\n\n/* genproof: a field-by-field copy (VST: no struct assignment) */\n'
             'MEM_STATIC void ZSTD_customMem_copy(ZSTD_customMem* dst, const ZSTD_customMem* src)\n{\n'
             '    dst->customAlloc = src->customAlloc;\n    dst->customFree = src->customFree;\n    dst->opaque = src->opaque;\n}\n\n') + s[b:]
save(p, s)


def alloc_calls(s, cnt):
    """ZSTD_custom{Malloc,Calloc,Free}(x, M) -> ...P(x, &M), or (x, customMem) where customMem is now a pointer."""
    def r(m):
        mem = m.group('m')
        return 'ZSTD_custom%sP(%s, %s)' % (m.group(1), m.group('a'), mem if mem == 'customMem' else '&' + mem)
    return resub(s, r'ZSTD_custom(Malloc|Calloc|Free)\((?P<a>[^;]*?), (?P<m>customMem|ddict->cMem|cMem|zds->customMem|dctx->customMem)\)', r, cnt)


# ---------------------------------------------------------------------------------------------------------
# decompress/zstd_ddict.c, zstd_ddict.h: ZSTD_createDDict_advancedP (allocator by pointer); copies of cMem.
p = 'lib/decompress/zstd_ddict.c'
s = load(p)
s = alloc_calls(s, 4)
old_sig = ('ZSTD_DDict* ZSTD_createDDict_advanced(const void* dict, size_t dictSize,\n'
           '                                      ZSTD_dictLoadMethod_e dictLoadMethod,\n'
           '                                      ZSTD_dictContentType_e dictContentType,\n'
           '                                      ZSTD_customMem customMem)\n{\n'
           '    if ((!customMem.customAlloc) ^ (!customMem.customFree)) return NULL;\n')
new_sig = ('ZSTD_DDict* ZSTD_createDDict_advancedP(const void* dict, size_t dictSize,   /* genproof: allocator by pointer */\n'
           '                                      ZSTD_dictLoadMethod_e dictLoadMethod,\n'
           '                                      ZSTD_dictContentType_e dictContentType,\n'
           '                                      const ZSTD_customMem* customMem)\n{\n'
           '    if ((!customMem->customAlloc) ^ (!customMem->customFree)) return NULL;\n')
s = rep(s, old_sig, new_sig)
s = rep(s, '        ddict->cMem = customMem;\n',
        '        ZSTD_customMem_copy(&ddict->cMem, customMem);   /* genproof: was ddict->cMem = customMem */\n')
s = rep(s, '/*! ZSTD_createDDict() :\n',
        '#ifndef GP_NO_STRUCT_API   /* genproof: a struct parameter; the decoder calls ZSTD_createDDict_advancedP */\n'
        'ZSTD_DDict* ZSTD_createDDict_advanced(const void* dict, size_t dictSize,\n'
        '                                      ZSTD_dictLoadMethod_e dictLoadMethod,\n'
        '                                      ZSTD_dictContentType_e dictContentType,\n'
        '                                      ZSTD_customMem customMem)\n{\n'
        '    return ZSTD_createDDict_advancedP(dict, dictSize, dictLoadMethod, dictContentType, &customMem);\n}\n#endif\n\n'
        '/*! ZSTD_createDDict() :\n')
s = resub(s, r'return ZSTD_createDDict_advanced\((dict\w*), dictSize, (ZSTD_dlm_by\w+), ZSTD_dct_auto, allocator\);',
          r'return ZSTD_createDDict_advancedP(\1, dictSize, \2, ZSTD_dct_auto, &allocator);   /* genproof: by pointer */', 2)
s = rep(s, '    {   ZSTD_customMem const cMem = ddict->cMem;\n',
        '    {   ZSTD_customMem cMem;\n        ZSTD_customMem_copy(&cMem, &ddict->cMem);   /* genproof: was ZSTD_customMem const cMem = ddict->cMem */\n')
save(p, s)
p = 'lib/decompress/zstd_ddict.h'
s = load(p)
s = rep(s, 'size_t ZSTD_DDict_dictSize(const ZSTD_DDict* ddict);\n',
        'size_t ZSTD_DDict_dictSize(const ZSTD_DDict* ddict);\n'
        '/* genproof: ZSTD_createDDict_advanced with the allocator by pointer (VST: no struct parameters) */\n'
        'ZSTD_DDict* ZSTD_createDDict_advancedP(const void* dict, size_t dictSize, ZSTD_dictLoadMethod_e dictLoadMethod,\n'
        '                                       ZSTD_dictContentType_e dictContentType, const ZSTD_customMem* customMem);\n')
save(p, s)

# ---------------------------------------------------------------------------------------------------------
# decompress/zstd_decompress.c
p = 'lib/decompress/zstd_decompress.c'
s = load(p)
s = alloc_calls(s, 12)
for f in ('static size_t ZSTD_DDictHashSet_expand(ZSTD_DDictHashSet* hashSet, ZSTD_customMem customMem) {',
          'static ZSTD_DDictHashSet* ZSTD_createDDictHashSet(ZSTD_customMem customMem) {',
          'static void ZSTD_freeDDictHashSet(ZSTD_DDictHashSet* hashSet, ZSTD_customMem customMem) {',
          'static size_t ZSTD_DDictHashSet_addDDict(ZSTD_DDictHashSet* hashSet, const ZSTD_DDict* ddict, ZSTD_customMem customMem) {',
          'static ZSTD_DCtx* ZSTD_createDCtx_internal(ZSTD_customMem customMem) {'):
    s = rep(s, f, f.replace('ZSTD_customMem customMem', 'const ZSTD_customMem* customMem') + '   /* genproof: allocator by pointer */')
s = rep(s, '    if ((!customMem.customAlloc) ^ (!customMem.customFree)) return NULL;\n',
        '    if ((!customMem->customAlloc) ^ (!customMem->customFree)) return NULL;\n')
s = rep(s, '        dctx->customMem = customMem;\n',
        '        ZSTD_customMem_copy(&dctx->customMem, customMem);   /* genproof: was dctx->customMem = customMem */\n')
s = rep(s, 'ZSTD_createDCtx_internal(ZSTD_defaultCMem)', 'ZSTD_createDCtx_internal(&ZSTD_defaultCMem)', 3)
s = rep(s, 'ZSTD_DCtx* ZSTD_createDCtx_advanced(ZSTD_customMem customMem)\n{\n    return ZSTD_createDCtx_internal(customMem);\n}\n',
        '#ifndef GP_NO_STRUCT_API   /* genproof: a struct parameter */\n'
        'ZSTD_DCtx* ZSTD_createDCtx_advanced(ZSTD_customMem customMem)\n{\n    return ZSTD_createDCtx_internal(&customMem);\n}\n#endif\n')
s = rep(s, 'ZSTD_DStream* ZSTD_createDStream_advanced(ZSTD_customMem customMem)\n{\n    return ZSTD_createDCtx_internal(customMem);\n}\n',
        '#ifndef GP_NO_STRUCT_API   /* genproof: a struct parameter */\n'
        'ZSTD_DStream* ZSTD_createDStream_advanced(ZSTD_customMem customMem)\n{\n    return ZSTD_createDCtx_internal(&customMem);\n}\n#endif\n')
s = rep(s, '    {   ZSTD_customMem const cMem = dctx->customMem;\n',
        '    {   ZSTD_customMem cMem;\n        ZSTD_customMem_copy(&cMem, &dctx->customMem);   /* genproof: was ZSTD_customMem const cMem = dctx->customMem */\n')
s = rep(s, 'ZSTD_freeDDictHashSet(dctx->ddictSet, cMem);', 'ZSTD_freeDDictHashSet(dctx->ddictSet, &cMem);')
s = rep(s, 'ZSTD_createDDictHashSet(dctx->customMem);', 'ZSTD_createDDictHashSet(&dctx->customMem);')
s = rep(s, 'ZSTD_DDictHashSet_addDDict(dctx->ddictSet, ddict, dctx->customMem)', 'ZSTD_DDictHashSet_addDDict(dctx->ddictSet, ddict, &dctx->customMem)')
s = rep(s, 'ZSTD_createDDict_advanced(dict, dictSize, dictLoadMethod, dictContentType, dctx->customMem);',
        'ZSTD_createDDict_advancedP(dict, dictSize, dictLoadMethod, dictContentType, &dctx->customMem);   /* genproof: by pointer */')

# ZSTD_frameSizeInfo: out-pointers instead of struct returns
s = rep(s, 'static ZSTD_frameSizeInfo ZSTD_errorFrameSizeInfo(size_t ret)\n{\n'
           '    ZSTD_frameSizeInfo frameSizeInfo;\n'
           '    frameSizeInfo.compressedSize = ret;\n'
           '    frameSizeInfo.decompressedBound = ZSTD_CONTENTSIZE_ERROR;\n'
           '    return frameSizeInfo;\n}\n',
        'static void ZSTD_errorFrameSizeInfo(ZSTD_frameSizeInfo* frameSizeInfo, size_t ret)   /* genproof: out-pointer, was a struct return */\n{\n'
        '    frameSizeInfo->compressedSize = ret;\n'
        '    frameSizeInfo->decompressedBound = ZSTD_CONTENTSIZE_ERROR;\n}\n')
a = s.index('static ZSTD_frameSizeInfo ZSTD_findFrameSizeInfo(const void* src, size_t srcSize, ZSTD_format_e format)')
b = s.index('static size_t ZSTD_findFrameCompressedSize_advanced(')
f = s[a:b]
f = rep(f, 'static ZSTD_frameSizeInfo ZSTD_findFrameSizeInfo(const void* src, size_t srcSize, ZSTD_format_e format)',
        'static void ZSTD_findFrameSizeInfo(ZSTD_frameSizeInfo* frameSizeInfo, const void* src, size_t srcSize, ZSTD_format_e format)   /* genproof: out-pointer, was a struct return */')
f = rep(f, '    ZSTD_frameSizeInfo frameSizeInfo;\n    ZSTD_memset(&frameSizeInfo, 0, sizeof(ZSTD_frameSizeInfo));\n',
        '    ZSTD_memset(frameSizeInfo, 0, sizeof(ZSTD_frameSizeInfo));\n')
f = rep(f, 'return ZSTD_findFrameSizeInfoLegacy(src, srcSize);', '{ *frameSizeInfo = ZSTD_findFrameSizeInfoLegacy(src, srcSize); return; }   /* genproof: legacy only (off) */')
f = resub(f, r'return ZSTD_errorFrameSizeInfo\(([^;]*)\);', r'{ ZSTD_errorFrameSizeInfo(frameSizeInfo, \1); return; }', 5)
f = rep(f, 'frameSizeInfo.', 'frameSizeInfo->', 6)
f = rep(f, 'return frameSizeInfo;', 'return;', 2)
s = s[:a] + f + s[b:]
s = resub(s, r'ZSTD_frameSizeInfo const frameSizeInfo = ZSTD_findFrameSizeInfo\(',
          'ZSTD_frameSizeInfo frameSizeInfo; ZSTD_findFrameSizeInfo(&frameSizeInfo, ', 3)

# ZSTD_bounds: an internal out-pointer version; the public struct-returning one on top of it
a = s.index('ZSTD_bounds ZSTD_dParam_getBounds(ZSTD_dParameter dParam)\n{')
b = s.index('/* ZSTD_dParam_withinBounds:')
f = s[a:b]
f = rep(f, 'ZSTD_bounds ZSTD_dParam_getBounds(ZSTD_dParameter dParam)\n{\n    ZSTD_bounds bounds = { 0, 0, 0 };\n',
        'static void ZSTD_dParam_getBoundsP(ZSTD_bounds* bounds, ZSTD_dParameter dParam)   /* genproof: out-pointer, was a struct return */\n{\n'
        '    bounds->error = 0; bounds->lowerBound = 0; bounds->upperBound = 0;\n')
f = rep(f, 'bounds.', 'bounds->', 15)
f = rep(f, 'return bounds;', 'return;', 8)
f = rep(f, '        default:;\n', '        default: break;   /* genproof: was `default:;` (VST\'s switch rule) */\n')
f += ('#ifndef GP_NO_STRUCT_API   /* genproof: a struct return */\n'
      'ZSTD_bounds ZSTD_dParam_getBounds(ZSTD_dParameter dParam)\n{\n'
      '    ZSTD_bounds bounds;\n    ZSTD_dParam_getBoundsP(&bounds, dParam);\n    return bounds;\n}\n#endif\n\n')
s = s[:a] + f + s[b:]
s = rep(s, '/* ZSTD_DCtx_setMaxWindowSize() :\n',
        '/* genproof: the out-pointer version of ZSTD_dParam_getBounds, defined below */\n'
        'static void ZSTD_dParam_getBoundsP(ZSTD_bounds* bounds, ZSTD_dParameter dParam);\n\n'
        '/* ZSTD_DCtx_setMaxWindowSize() :\n')
s = resub(s, r'ZSTD_bounds const bounds = ZSTD_dParam_getBounds\(([^;]*)\);',
          r'ZSTD_bounds bounds; ZSTD_dParam_getBoundsP(&bounds, \1);   /* genproof: out-pointer */', 2)

# ZSTD_outBuffer copies
s = rep(s, 'static size_t ZSTD_checkOutBuffer(',
        '/* genproof: a field-by-field copy (VST: no struct assignment) */\n'
        'static void ZSTD_outBuffer_copy(ZSTD_outBuffer* dst, const ZSTD_outBuffer* src)\n{\n'
        '    dst->dst = src->dst;\n    dst->size = src->size;\n    dst->pos = src->pos;\n}\n\n'
        'static size_t ZSTD_checkOutBuffer(')
# not a field-by-field copy here: on the first call expectedOutBuffer was never written, and reading its fields
# one by one is stuck where the struct copy copied the unwritten bytes as they are; it is only read later, when
# it has been written (stable output mode, after init), and zds does not change in between
s = rep(s, '    ZSTD_outBuffer const expect = zds->expectedOutBuffer;\n',
        '    ZSTD_outBuffer const* const expect = &zds->expectedOutBuffer;   /* genproof: was a struct copy (ZSTD_outBuffer const expect = ...) */\n')
s = rep(s, '    if (expect.dst == output->dst && expect.pos == output->pos && expect.size == output->size)\n',
        '    if (expect->dst == output->dst && expect->pos == output->pos && expect->size == output->size)\n')
s = rep(s, 'zds->expectedOutBuffer = *output;', 'ZSTD_outBuffer_copy(&zds->expectedOutBuffer, output);   /* genproof: was zds->expectedOutBuffer = *output */', 2)
save(p, s)

# ---------------------------------------------------------------------------------------------------------
# decompress/zstd_decompress_block.c: seq_t by pointer, ZSTD_decodeSequence and ZSTD_getOffsetInfo to out-pointers
p = 'lib/decompress/zstd_decompress_block.c'
s = load(p)
s = rep(s, '} seq_t;\n',
        '} seq_t;\n\n/* genproof: a field-by-field copy (VST: no struct assignment) */\n'
        'MEM_STATIC void ZSTD_seqCopy(seq_t* dst, const seq_t* src)\n{\n'
        '    dst->litLength = src->litLength;\n    dst->matchLength = src->matchLength;\n    dst->offset = src->offset;\n}\n')
LOCAL = '    seq_t sequence;   /* genproof: the by-value parameter, copied field by field (it is modified below) */\n    ZSTD_seqCopy(&sequence, gp_sequence);\n'
for name, cnt in (('ZSTD_execSequenceEnd', 1), ('ZSTD_execSequenceEndSplitLitBuffer', 1), ('ZSTD_execSequence', 1),
                  ('ZSTD_execSequenceSplitLitBuffer', 1)):
    m = re.search(r'size_t %s\(BYTE\* op,\n(.*?)\n\{\n' % re.escape(name), s, re.S)
    assert m, name
    sig = m.group(0)
    new = rep(sig, 'seq_t sequence,', 'const seq_t* gp_sequence,')
    s = s[:m.start()] + new + LOCAL + s[m.end():]
m = re.search(r'size_t ZSTD_prefetchMatch\(size_t prefetchPos, seq_t const sequence,\n(.*?)\n\{\n', s, re.S)
s = s[:m.start()] + rep(m.group(0), 'seq_t const sequence,', 'const seq_t* gp_sequence,') + \
    '    seq_t sequence;   /* genproof: the by-value parameter, copied field by field */\n    ZSTD_seqCopy(&sequence, gp_sequence);\n' + s[m.end():]
# calls: the sequence argument by address (a pointer argument `*p` becomes `p`)
s = by_pointer(s, 'ZSTD_execSequenceEnd', 2, 1)
s = by_pointer(s, 'ZSTD_execSequenceEndSplitLitBuffer', 3, 1)
s = by_pointer(s, 'ZSTD_execSequence', 2, 7)
s = by_pointer(s, 'ZSTD_execSequenceSplitLitBuffer', 3, 3)
s = by_pointer(s, 'ZSTD_prefetchMatch', 1, 3)
s = resub(s, r'sequences\[([^\]]*)\] = sequence;', r'ZSTD_seqCopy(&sequences[\1], &sequence);   /* genproof: was sequences[\1] = sequence */', 3)
# ZSTD_decodeSequence: an out-pointer
s = rep(s, 'FORCE_INLINE_TEMPLATE seq_t\nZSTD_decodeSequence(seqState_t* seqState, const ZSTD_longOffset_e longOffsets, const int isLastSeq)\n',
        'FORCE_INLINE_TEMPLATE void   /* genproof: out-pointer gp_seq, was a struct return */\n'
        'ZSTD_decodeSequence(seq_t* gp_seq, seqState_t* seqState, const ZSTD_longOffset_e longOffsets, const int isLastSeq)\n')
s = rep(s, '    return seq;\n}\n', '    ZSTD_seqCopy(gp_seq, &seq);   /* genproof: was return seq */\n}\n')
s = resub(s, r'seq_t (?:const )?sequence = ZSTD_decodeSequence\(&seqState, ',
          'seq_t sequence; ZSTD_decodeSequence(&sequence, &seqState, ', 4)
s = resub(s, r'(\n\s+)sequence = ZSTD_decodeSequence\(&seqState, ', r'\1ZSTD_decodeSequence(&sequence, &seqState, ', 1)
# ZSTD_getOffsetInfo: an out-pointer
s = rep(s, 'static ZSTD_OffsetInfo\nZSTD_getOffsetInfo(const ZSTD_seqSymbol* offTable, int nbSeq)\n',
        'static void   /* genproof: out-pointer gp_info, was a struct return */\nZSTD_getOffsetInfo(ZSTD_OffsetInfo* gp_info, const ZSTD_seqSymbol* offTable, int nbSeq)\n')
s = rep(s, '    return info;\n}\n',
        '    gp_info->longOffsetShare = info.longOffsetShare;   /* genproof: was return info */\n'
        '    gp_info->maxNbAdditionalBits = info.maxNbAdditionalBits;\n}\n')
s = rep(s, 'ZSTD_OffsetInfo const info = ZSTD_getOffsetInfo(dctx->OFTptr, nbSeq);',
        'ZSTD_OffsetInfo info; ZSTD_getOffsetInfo(&info, dctx->OFTptr, nbSeq);   /* genproof: out-pointer */')
save(p, s)

# ---------------------------------------------------------------------------------------------------------
# decompress/huf_decompress.c: DTableDesc and HUF_DEltX2 by out-pointer, HUF_DEltX1 copies field by field
p = 'lib/decompress/huf_decompress.c'
s = load(p)
s = rep(s, 'static DTableDesc HUF_getDTableDesc(const HUF_DTable* table)\n{\n'
           '    DTableDesc dtd;\n    ZSTD_memcpy(&dtd, table, sizeof(dtd));\n    return dtd;\n}\n',
        'static void HUF_getDTableDesc(DTableDesc* dtd, const HUF_DTable* table)   /* genproof: out-pointer, was a struct return */\n{\n'
        '    ZSTD_memcpy(dtd, table, sizeof(*dtd));\n}\n\n'
        '/* genproof: the tableLog field of the descriptor (was HUF_getDTableDesc(table).tableLog) */\n'
        'static U32 HUF_getDTableLog(const HUF_DTable* table)\n{\n'
        '    DTableDesc dtd;\n    HUF_getDTableDesc(&dtd, table);\n    return dtd.tableLog;\n}\n')
s = rep(s, 'U32 const dtLog = HUF_getDTableDesc(DTable).tableLog;', 'U32 const dtLog = HUF_getDTableLog(DTable);   /* genproof */')
s = resub(s, r'DTableDesc (?:const )?dtd = HUF_getDTableDesc\(DTable\);',
          'DTableDesc dtd; HUF_getDTableDesc(&dtd, DTable);   /* genproof: out-pointer */', 8)
s = rep(s, 'static HUF_DEltX2 HUF_buildDEltX2(U32 symbol, U32 nbBits, U32 baseSeq, int level)\n{\n'
           '    HUF_DEltX2 DElt;\n'
           '    U32 const val = HUF_buildDEltX2U32(symbol, nbBits, baseSeq, level);\n'
           '    DEBUG_STATIC_ASSERT(sizeof(DElt) == sizeof(val));\n'
           '    ZSTD_memcpy(&DElt, &val, sizeof(val));\n'
           '    return DElt;\n}\n',
        'static void HUF_buildDEltX2(HUF_DEltX2* DElt, U32 symbol, U32 nbBits, U32 baseSeq, int level)   /* genproof: out-pointer, was a struct return */\n{\n'
        '    U32 const val = HUF_buildDEltX2U32(symbol, nbBits, baseSeq, level);\n'
        '    DEBUG_STATIC_ASSERT(sizeof(*DElt) == sizeof(val));\n'
        '    ZSTD_memcpy(DElt, &val, sizeof(val));\n}\n')
s = rep(s, '            HUF_DEltX2 const DElt = HUF_buildDEltX2(ptr->symbol, nbBits, baseSeq, level);\n'
           '            *DTableRank++ = DElt;\n',
        '            HUF_buildDEltX2(DTableRank, ptr->symbol, nbBits, baseSeq, level);   /* genproof: was DElt = ...; *DTableRank = DElt */\n'
        '            DTableRank++;\n')
s = rep(s, '            HUF_DEltX2 const DElt = HUF_buildDEltX2(ptr->symbol, nbBits, baseSeq, level);\n'
           '            DTableRank[0] = DElt;\n'
           '            DTableRank[1] = DElt;\n',
        '            HUF_buildDEltX2(&DTableRank[0], ptr->symbol, nbBits, baseSeq, level);   /* genproof: was DElt = ...; DTableRank[0] = DTableRank[1] = DElt */\n'
        '            HUF_buildDEltX2(&DTableRank[1], ptr->symbol, nbBits, baseSeq, level);\n')
s = resub(s, r'(\s+)dt\[(uStart(?:\+[01])?)\] = D;',
          r'\1dt[\2].nbBits = D.nbBits; dt[\2].byte = D.byte;   /* genproof: was dt[\2] = D */', 3)
s = rep(s, '                    ZSTD_memcpy(DTable + i + 6, &DEltX2, sizeof(DEltX2));\n'
           '                }\n'
           '            }\n'
           '        }\n',
        '                    ZSTD_memcpy(DTable + i + 6, &DEltX2, sizeof(DEltX2));\n'
        '                }\n'
        '            }\n'
        '            break;   /* genproof: the last case ended without break (VST\'s switch rule) */\n'
        '        }\n')
# The X2 fills (HUF_fillDTableX2ForWeight cases 4, 8, default; the skip fill of HUF_fillDTableX2Level2) build two
# cells in a U64 and copy its 8 bytes; VST cannot read the bytes (or the U16/BYTE fields) back from a stored U64
# (found while proving).  The same bytes, as two U32 copies of the cell: the U64 is the
# cell twice (HUF_buildDEltX2U64: DElt + (DElt << 32)), so cells j and j + 1 get the U32 on either endianness.
s = rep(s, 'U64 const DEltX2 = HUF_buildDEltX2U64(', 'U32 const DElt2 = HUF_buildDEltX2U32(', 4)
s = resub(s, r'ZSTD_memcpy\(([^,;]+), &DEltX2, sizeof\(DEltX2\)\);',
          r'ZSTD_memcpy(\1, &DElt2, sizeof(DElt2)); ZSTD_memcpy(\1 + 1, &DElt2, sizeof(DElt2));   /* genproof: was one U64 copy of two cells */', 17)
save(p, s)

# ---------------------------------------------------------------------------------------------------------
# common/fse.h: FSE_decode_t copies field by field
p = 'lib/common/fse.h'
s = load(p)
s = rep(s, '} FSE_decode_t;   /* size == U32 */\n',
        '} FSE_decode_t;   /* size == U32 */\n\n/* genproof: a field-by-field copy (VST: no struct assignment) */\n'
        'MEM_STATIC void FSE_decode_copy(FSE_decode_t* dst, const FSE_decode_t* src)\n{\n'
        '    dst->newState = src->newState;\n    dst->symbol = src->symbol;\n    dst->nbBits = src->nbBits;\n}\n')
s = rep(s, '    FSE_decode_t const DInfo = ((const FSE_decode_t*)(DStatePtr->table))[DStatePtr->state];\n',
        '    FSE_decode_t DInfo;   /* genproof: was a struct copy of the table entry */\n'
        '    FSE_decode_copy(&DInfo, &((const FSE_decode_t*)(DStatePtr->table))[DStatePtr->state]);\n', 4)
save(p, s)

# ---------------------------------------------------------------------------------------------------------
# common/mem.h: MEM_write64 as eight byte stores.  VST's `mapsto tulong (Vlong x)` also holds of eight fragments of
# the value, each of which reads back as an undefined byte, so the bytes of a U64 copied out of a local cannot be
# derived; 2- and 4-byte scalars do not have this problem.  The
# decoder writes U64s with MEM_write64 into byte tables (the FSE spread, the Huffman X1 table) and reads them back as
# bytes.  Little-endian order is the native one of the verified target (x86-64); a big-endian target keeps the copy.
s = load('lib/common/mem.h')
s = rep(s, """MEM_STATIC void MEM_write64(void* memPtr, U64 value)
{
    ZSTD_memcpy(memPtr, &value, sizeof(value));
}""", """MEM_STATIC void MEM_write64(void* memPtr, U64 value)
{   /* genproof: was ZSTD_memcpy(memPtr, &value, sizeof(value)) (VST cannot give the bytes of a stored U64) */
#if defined(__BYTE_ORDER__) && defined(__ORDER_BIG_ENDIAN__) && (__BYTE_ORDER__ == __ORDER_BIG_ENDIAN__)
    ZSTD_memcpy(memPtr, &value, sizeof(value));
#else
    BYTE* const p = (BYTE*)memPtr;
    p[0] = (BYTE)value;
    p[1] = (BYTE)(value >> 8);
    p[2] = (BYTE)(value >> 16);
    p[3] = (BYTE)(value >> 24);
    p[4] = (BYTE)(value >> 32);
    p[5] = (BYTE)(value >> 40);
    p[6] = (BYTE)(value >> 48);
    p[7] = (BYTE)(value >> 56);
#endif
}""")
save('lib/common/mem.h', s)

# ---------------------------------------------------------------------------------------------------------
# common/bitstream.h: BIT_initDStream's `switch(srcSize)` on a size_t.  VST's only switch rule (semax_switch) needs an
# int scrutinee (is_int_type holds only for Tint), so a switch on a long has no proof rule.
# The branch is `srcSize < sizeof(bitD->bitContainer)` = 8: the cast
# is exact and every case keeps its value.
s = load('lib/common/bitstream.h')
s = rep(s, '        switch(srcSize)\n',
        '        switch((unsigned)srcSize)   /* genproof: was switch(srcSize): VST has no switch rule for a long; here srcSize < 8 */\n')
save('lib/common/bitstream.h', s)

# ---------------------------------------------------------------------------------------------------------
# ZSTD_checkContinuity compares the output with previousDstEnd (`dst != dctx->previousDstEnd`).  After a dictionary
# made by copy (ZSTD_createDDict, ZSTD_DCtx_loadDictionary), previousDstEnd is the end of zstd's own copy: a pointer one
# past the end of another object, which ISO C compares and CompCert's semantics (VST's) does not.  A flag records that
# case and skips the comparison: the output is not contiguous with zstd's private copy (were it, by chance, adjacent in
# memory, both paths read the same dictionary bytes and decode the same).  Found by the laws any_dict_copy and
# valid_dict_copy (interpreter stop in ZSTD_checkContinuity).
p = 'lib/decompress/zstd_decompress_internal.h'
s = load(p)
s = rep(s, '    const void* previousDstEnd;   /* detect continuity */\n',
        '    const void* previousDstEnd;   /* detect continuity */\n'
        '    int gpDictCopy;               /* genproof: previousDstEnd is the end of zstd\'s own copy of a dictionary */\n')
save(p, s)
p = 'lib/decompress/zstd_ddict.c'
s = load(p)
s = rep(s, '    dctx->previousDstEnd = dctx->dictEnd;\n',
        '    dctx->previousDstEnd = dctx->dictEnd;\n'
        '    dctx->gpDictCopy = ddict->dictBuffer != NULL;   /* genproof: a dictionary made by copy */\n')
save(p, s)
p = 'lib/decompress/zstd_decompress_block.c'
s = load(p)
s = rep(s, '    if (dst != dctx->previousDstEnd && dstSize > 0) {   /* not contiguous */\n',
        '    if (dstSize > 0 && (dctx->gpDictCopy || dst != dctx->previousDstEnd)) {   /* not contiguous */   /* genproof: was (dst != dctx->previousDstEnd) && dstSize > 0 (gpDictCopy: never contiguous with zstd\'s copy; dstSize first: dst may be one past the end of the output when a frame filled it, and previousDstEnd in another object, a 0-byte copied dictionary) */\n')
s = rep(s, '        dctx->previousDstEnd = dst;\n', '        dctx->previousDstEnd = dst;\n        dctx->gpDictCopy = 0;   /* genproof */\n')
s = rep(s, '    dctx->previousDstEnd = (char*)dst + dSize;\n', '    dctx->previousDstEnd = (char*)dst + dSize;\n    dctx->gpDictCopy = 0;   /* genproof */\n')
save(p, s)
p = 'lib/decompress/zstd_decompress.c'
s = load(p)
s = rep(s, '    dctx->previousDstEnd = (const char*)blockStart + blockSize;\n',
        '    dctx->previousDstEnd = (const char*)blockStart + blockSize;\n    dctx->gpDictCopy = 0;   /* genproof */\n')
s = rep(s, '            dctx->previousDstEnd = (char*)dst + rSize;\n',
        '            dctx->previousDstEnd = (char*)dst + rSize;\n            dctx->gpDictCopy = 0;   /* genproof */\n')
s = rep(s, '    dctx->previousDstEnd = (const char*)dict + dictSize;\n',
        '    dctx->previousDstEnd = (const char*)dict + dictSize;\n    dctx->gpDictCopy = 0;   /* genproof: the caller\'s dictionary, by reference */\n')
s = rep(s, '    dctx->previousDstEnd = NULL;\n', '    dctx->previousDstEnd = NULL;\n    dctx->gpDictCopy = 0;   /* genproof */\n')
save(p, s)

# ZSTD_DCtx_setParameter's empty default (reached from stable_out, ZSTD_d_stableOutBuffer): the case after
# ZSTD_d_maxBlockSize.  (ZSTD_DCtx_getParameter's is left alone: no law reaches it.)
p = 'lib/decompress/zstd_decompress.c'
s = load(p)
s = rep(s, '            dctx->maxBlockSizeParam = value;\n            return 0;\n        default:;\n',
        '            dctx->maxBlockSizeParam = value;\n            return 0;\n        default: break;   /* genproof: was `default:;` (VST\'s switch rule) */\n')
save(p, s)

# HUF_decodeStreamX2, first loop (dtLog <= 11): `p < pEnd-9` with pEnd - p = 8 forms p - 1; when the literal buffer
# starts a struct field (litExtraBuffer), VST needs ownership of the byte before it to compare.
# The distance inside the output instead: p <= pEnd holds there, so the test is the same.
p = 'lib/decompress/huf_decompress.c'
s = load(p)
s = rep(s, '            while ((BIT_reloadDStream(bitDPtr) == BIT_DStream_unfinished) & (p < pEnd-9)) {\n',
        '            while ((BIT_reloadDStream(bitDPtr) == BIT_DStream_unfinished) & ((size_t)(pEnd - p) > 9)) {   /* genproof: was p < pEnd-9 (p - 1 when pEnd - p = 8) */\n')
save(p, s)

# ZSTD_prefetchMatch: the prefetch address `ZSTD_wrappedPtrSub(ZSTD_wrappedPtrAdd(matchBase, pos), offset)` is
# NULL + pos when matchBase is a NULL dictEnd (no dictionary); zstd does this on purpose (compiler.h: "Zstd relies on
# pointer overflow in its decompressor", ZSTD_ALLOW_POINTER_OVERFLOW_ATTR), it is only a hint, and CompCert defines
# it, but VST cannot type pointer arithmetic on NULL.  The address is computed only from a non-NULL base (this build's
# PREFETCH_L1 does nothing with it; the helpers stay, so their proofs stay valid).  Same results.
p = 'lib/decompress/zstd_decompress_block.c'
s = load(p)
s = rep(s, '''        const BYTE* const match = (const BYTE*)ZSTD_wrappedPtrSub(ZSTD_wrappedPtrAdd(matchBase, (ptrdiff_t)prefetchPos), (ptrdiff_t)sequence.offset);
        PREFETCH_L1(match); PREFETCH_L1(ZSTD_wrappedPtrAdd(match, CACHELINE_SIZE));   /* note : it's safe to invoke PREFETCH() on any memory address, including invalid ones */
''', '''        if (matchBase != NULL) {   /* genproof: no prefetch address from NULL (NULL + pos); a hint only */
        const BYTE* const match = (const BYTE*)ZSTD_wrappedPtrSub(ZSTD_wrappedPtrAdd(matchBase, (ptrdiff_t)prefetchPos), (ptrdiff_t)sequence.offset);
        PREFETCH_L1(match); PREFETCH_L1(ZSTD_wrappedPtrAdd(match, CACHELINE_SIZE));   /* note : it's safe to invoke PREFETCH() on any memory address, including invalid ones */
        }
''')
save(p, s)

# The sequence executors' byte copies: ZSTD_overlapCopy8's first four bytes and the short and leftover loops of
# ZSTD_safecopy and ZSTD_safecopyDstBeforeSrc.  In Clight each byte goes through an unsigned char temp, and VST's load
# rule needs a defined byte there.  For any input these copies can read bytes never written (wildcopy's over-copied
# slack in the literal buffer and in the output, the streaming ring buffer after it wraps): defined in ISO C (unsigned
# char) and in CompCert (the byte stays undefined), but unprovable in VST.  Each byte is copied with a one-byte
# ZSTD_memmove instead, which moves bytes as they are (GenProof.Env's memmove_spec: two objects, or one array with any
# source and destination).  memmove, not memcpy: ZSTD_safecopyDstBeforeSrc's loop runs for any diff > -8, op == ip
# included (ZSTD_execSequenceEndSplitLitBuffer rejects only op > *litPtr), where a memcpy would be undefined.  Same
# results: the same byte moves, one at a time and forwards, so overlapping copies keep their order.
p = 'lib/decompress/zstd_decompress_block.c'
s = load(p)
for k in range(4):
    s = rep(s, '        (*op)[%d] = (*ip)[%d];\n' % (k, k),
            '        ZSTD_memmove(*op + %d, *ip + %d, 1);   /* genproof: was (*op)[%d] = (*ip)[%d]; (the byte as it is) */\n'
            % (k, k, k, k))
for ind in ('        ', '    '):
    s = rep(s, ind + 'while (op < oend) *op++ = *ip++;\n',
            ind + 'while (op < oend) { ZSTD_memmove(op, ip, 1); op++; ip++; }   /* genproof: was *op++ = *ip++; (bytes as they are) */\n',
            2)
save(p, s)

# HUF_decompress4X1/4X2_usingDTable_internal: function-pointer locals initialised and assigned with bare function
# designators (`fallbackFn = HUF_..._default`): in Clight an Sset of an expression of function type, for which VST has
# no rule (it evaluates `&f`).  The address taken explicitly at the sites that reach the Clight (the asm-loop
# assignments are compiled out in this configuration): the same pointer in C, where a designator decays to it.
p = 'lib/decompress/huf_decompress.c'
s = load(p)
for x in ('1', '2'):
    for old, new in (
            ('    HUF_DecompressUsingDTableFn fallbackFn = HUF_decompress4X%s_usingDTable_internal_default;\n' % x,
             '    HUF_DecompressUsingDTableFn fallbackFn = &HUF_decompress4X%s_usingDTable_internal_default;   /* genproof: & (VST: no bare function designator) */\n' % x),
            ('    HUF_DecompressFastLoopFn loopFn = HUF_decompress4X%s_usingDTable_internal_fast_c_loop;\n' % x,
             '    HUF_DecompressFastLoopFn loopFn = &HUF_decompress4X%s_usingDTable_internal_fast_c_loop;   /* genproof: & (VST) */\n' % x),
            ('        fallbackFn = HUF_decompress4X%s_usingDTable_internal_bmi2;\n' % x,
             '        fallbackFn = &HUF_decompress4X%s_usingDTable_internal_bmi2;   /* genproof: & (VST) */\n' % x)):
        s = rep(s, old, new)
save(p, s)

# ZSTD_decompressBegin_usingDDict: `dctx->ddictIsCold = (dctx->dictEnd != dictEnd)` compares the end of the new DDict's
# content (one past its object) with the context's dictEnd, which after a streaming ring wrap points into the output
# buffer (ZSTD_checkContinuity) and may point into an earlier DDict: two objects.  Defined in ISO C (6.5.9p6), but
# CompCert's semantics compares pointers into different blocks only when both are strictly valid, so the theorem's
# semantics is stuck (spec x_any_params).  The flag only steers
# the prefetch heuristics (PREFETCH_AREA, no effect on results) and the choice between the equivalent long and short
# sequence decoders for the first block, so it is set without the comparison: "cold", as for a new context.  This
# also removes the comparison with a possibly freed dictionary's end from this configuration.
p = 'lib/decompress/zstd_decompress.c'
s = load(p)
s = rep(s, '''        const char* const dictStart = (const char*)ZSTD_DDict_dictContent(ddict);
        size_t const dictSize = ZSTD_DDict_dictSize(ddict);
        const void* const dictEnd = dictStart + dictSize;
        dctx->ddictIsCold = (dctx->dictEnd != dictEnd);
''', '''        dctx->ddictIsCold = 1;   /* genproof: was (dctx->dictEnd != dictEnd), dictEnd the DDict content's end: pointers into two objects (CompCert); a heuristic */
''')
save(p, s)

print('vstpatch: 9 files patched', file=sys.stderr)
