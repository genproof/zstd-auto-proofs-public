// The decoding runs of the differential test (patch/diff.sh), compiled twice: as is against the patched
// decoder, and with -DORIG against the unmodified upstream library, whose symbols diff.sh renamed to
// orig_*.  Every run writes into fresh, exactly sized buffers.
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#ifdef ORIG
#define ZSTD_decompress           orig_ZSTD_decompress
#define ZSTD_isError              orig_ZSTD_isError
#define ZSTD_getErrorCode         orig_ZSTD_getErrorCode
#define ZSTD_createDStream        orig_ZSTD_createDStream
#define ZSTD_freeDStream          orig_ZSTD_freeDStream
#define ZSTD_initDStream          orig_ZSTD_initDStream
#define ZSTD_decompressStream     orig_ZSTD_decompressStream
#define ZSTD_createDCtx           orig_ZSTD_createDCtx
#define ZSTD_freeDCtx             orig_ZSTD_freeDCtx
#define ZSTD_decompress_usingDict orig_ZSTD_decompress_usingDict
#define ZSTD_createCCtx           orig_ZSTD_createCCtx
#define ZSTD_freeCCtx             orig_ZSTD_freeCCtx
#define ZSTD_CCtx_setParameter    orig_ZSTD_CCtx_setParameter
#define ZSTD_compress2            orig_ZSTD_compress2
#define ZSTD_compress_usingDict   orig_ZSTD_compress_usingDict
#define ZSTD_compressBound        orig_ZSTD_compressBound
#define P(f) orig_##f
#else
#define P(f) f
#endif
#define ZSTD_STATIC_LINKING_ONLY
#include "zstd.h"
#include "zstd_errors.h"

// A result as one number: the size on success, -(error code) on an error.
static long long res(size_t r) { return ZSTD_isError(r) ? -(long long)ZSTD_getErrorCode(r) : (long long)r; }

long long P(dt_oneshot)(unsigned char *dst, size_t cap, const unsigned char *src, size_t n)
{
	return res(ZSTD_decompress(dst, cap, src, n));
}

long long P(dt_dict)(unsigned char *dst, size_t cap, const unsigned char *src, size_t n,
                     const unsigned char *dict, size_t dn)
{
	ZSTD_DCtx *d = ZSTD_createDCtx();
	if (d == NULL)
		abort();
	long long r = res(ZSTD_decompress_usingDict(d, dst, cap, src, n, dict, dn));
	ZSTD_freeDCtx(d);
	return r;
}

/* the dictionary by copy (a ZSTD_DDict made by ZSTD_createDDict), twice (the second time "hot" in the original:
 * ddictIsCold 0, the short sequence decoder; always cold in vstpatch.py), then by ZSTD_DCtx_loadDictionary for another
 * decode with the same context: the paths of vstpatch.py's gpDictCopy */
long long P(dt_ddict)(unsigned char *dst, size_t cap, const unsigned char *src, size_t n,
                      const unsigned char *dict, size_t dn)
{
	ZSTD_DCtx *d = ZSTD_createDCtx();
	ZSTD_DDict *dd = ZSTD_createDDict(dict, dn);
	if (d == NULL || dd == NULL)
		abort();
	long long r = res(ZSTD_decompress_usingDDict(d, dst, cap, src, n, dd));
	if (r >= 0)
		r = res(ZSTD_decompress_usingDDict(d, dst, cap, src, n, dd));
	if (r >= 0 && !ZSTD_isError(ZSTD_DCtx_loadDictionary(d, dict, dn)))
		r = res(ZSTD_decompressDCtx(d, dst, cap, src, n));
	ZSTD_freeDDict(dd);
	ZSTD_freeDCtx(d);
	return r;
}

// Streaming with input and output chunks of the sizes in `chunks` (cycled), each in a fresh buffer of
// exactly that size.  The output goes to acc (capacity cap); *got = bytes delivered.
long long P(dt_stream)(unsigned char *acc, size_t cap, size_t *got, const unsigned char *src, size_t n,
                       const size_t *chunks, size_t nchunks)
{
	ZSTD_DStream *ds = ZSTD_createDStream();
	if (ds == NULL)
		abort();
	ZSTD_initDStream(ds);
	size_t ipos = 0, r = 0, k = 0;
	*got = 0;
	for (int steps = 0; steps < 1000000; steps++) {
		size_t ilen = chunks[k++ % nchunks], olen = chunks[k++ % nchunks];
		if (ilen > n - ipos)
			ilen = n - ipos;
		unsigned char *ib = malloc(ilen ? ilen : 1), *ob = malloc(olen);
		memcpy(ib, src + ipos, ilen);
		ZSTD_inBuffer in = { ib, ilen, 0 };
		ZSTD_outBuffer out = { ob, olen, 0 };
		r = ZSTD_decompressStream(ds, &out, &in);
		size_t take = out.pos <= cap - *got ? out.pos : cap - *got;
		memcpy(acc + *got, ob, take);
		*got += take;
		ipos += in.pos;
		free(ib);
		free(ob);
		if (ZSTD_isError(r) || r == 0 || (ipos == n && in.pos == 0 && out.pos == 0) || *got == cap)
			break;
	}
	ZSTD_freeDStream(ds);
	return res(r);
}

#ifdef ORIG
// Frames for the test, made by the upstream compressor.
size_t dt_compress(unsigned char *dst, size_t cap, const unsigned char *src, size_t n, int level,
                   int checksum, int content_size, const unsigned char *dict, size_t dn)
{
	ZSTD_CCtx *c = ZSTD_createCCtx();
	if (c == NULL)
		abort();
	size_t r;
	if (dict != NULL) {
		r = ZSTD_compress_usingDict(c, dst, cap, src, n, dict, dn, level);
	} else {
		ZSTD_CCtx_setParameter(c, ZSTD_c_compressionLevel, level);
		ZSTD_CCtx_setParameter(c, ZSTD_c_checksumFlag, checksum);
		ZSTD_CCtx_setParameter(c, ZSTD_c_contentSizeFlag, content_size);
		r = ZSTD_compress2(c, dst, cap, src, n);
	}
	ZSTD_freeCCtx(c);
	return ZSTD_isError(r) ? 0 : r;
}
size_t dt_bound(size_t n) { return ZSTD_compressBound(n); }
#endif
