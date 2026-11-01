// Law any_bufferless (PROMISES.md: S1, S2, S9; zstd's experimental buffer-less streaming decompression): ANY bytes
// fed to ZSTD_decompressContinue in pieces of the size ZSTD_nextSrcSizeToDecompress asks for or of ANY size ("requires
// this _exact_ amount of bytes, or it will fail"), into an output buffer of ANY size used front to back, after
// ZSTD_decompressBegin, ZSTD_decompressBegin_usingDict with a dictionary of ANY bytes, or ZSTD_decompressBegin_usingDDict
// with a ZSTD_DDict made of them; after a fully decoded frame or an error, decoding begins again (the context "can then
// be reset to start a new decompression") on the rest of the input.
//
// Claim (QuickProof.Contract.harness_safe of this program): no execution has undefined behaviour, and every gp_assert
// holds: ZSTD_decompressContinue returns an error or "the number of bytes regenerated within 'dst' (necessarily <=
// dstCapacity)".  Each piece of input is a fresh buffer of exactly its size.  The output and a dictionary used by
// reference are two regions of one allocation [dst | 1 byte | dict] (any_dict explains why).  Draw order n, bytes,
// cap (env.c); the rest comes from nondet_u32.
#include <stdlib.h>
#include "quickproof.h"
#ifndef ZSTD_STATIC_LINKING_ONLY
#define ZSTD_STATIC_LINKING_ONLY   /* the buffer-less API */
#endif
#include "zstd.h"

#define SRC_MAX 4096
#define DST_MAX 65536
#define DICT_MAX 512
#define CALLS_MAX 512

int main(void)
{
	size_t n = nondet_size(), cap, dn, ipos = 0, pos = 0, r, i;
	unsigned char *src, *buf, *dst, *dict, *ib;
	unsigned mode, calls;
	int begun = 0;
	ZSTD_DCtx *dctx;
	ZSTD_DDict *ddict = NULL;
	gp_assume(n <= SRC_MAX);
	src = malloc(n);
	if (src == NULL)
		return 0;                       /* harness out of memory: end the run */
	nondet_bytes(src, n);
	cap = nondet_size();
	gp_assume(cap <= DST_MAX);
	mode = nondet_u32() % 3;
	dn = mode == 0 ? 0 : nondet_u32() % (DICT_MAX + 1);
	buf = malloc(cap + 1 + dn);
	dctx = ZSTD_createDCtx();
	dst = buf;
	dict = NULL;
	if (buf != NULL)
		dict = buf + cap + 1;           /* not on NULL: NULL + n is undefined (C11 6.5.6p8) */
	if (buf == NULL || dctx == NULL) {
		free(src);
		free(buf);
		ZSTD_freeDCtx(dctx);
		return 0;
	}
	if (dn > 0)
		nondet_bytes(dict, dn);
	if (mode == 2)
		ddict = ZSTD_createDDict(dict, dn);   /* NULL on out of memory or a refused dictionary: Begin fails */
	for (calls = 0; calls < CALLS_MAX && ipos < n; calls++) {
		size_t want, len;
		if (!begun) {
			r = mode == 0 ? ZSTD_decompressBegin(dctx) : mode == 1 ? ZSTD_decompressBegin_usingDict(dctx, dict, dn)
			    : ZSTD_decompressBegin_usingDDict(dctx, ddict);
			if (ZSTD_isError(r))
				break;
			begun = 1;
		}
		want = ZSTD_nextSrcSizeToDecompress(dctx);
		if (want == 0) {
			begun = 0;                  /* a frame is fully decoded: begin the next one */
			continue;
		}
		len = nondet_u32() % 2 ? want : (size_t) nondet_u32() % (n - ipos + 1);
		if (len > n - ipos)
			len = n - ipos;
		ib = malloc(len > 0 ? len : 1);
		if (ib == NULL)
			break;                      /* harness out of memory: end the run */
		for (i = 0; i < len; i++)
			ib[i] = src[ipos + i];
		r = ZSTD_decompressContinue(dctx, dst + pos, cap - pos, ib, len);
		free(ib);
		gp_assert(ZSTD_isError(r) || r <= cap - pos);
		ipos += len;
		if (ZSTD_isError(r))
			begun = 0;                  /* reset: begin again on the rest */
		else
			pos += r;
	}
	ZSTD_freeDDict(ddict);
	ZSTD_freeDCtx(dctx);
	free(src);
	free(buf);
	return 0;
}
