// Law any_params (PROMISES.md: S1, S3, S4, S6, S8): decompression of ANY bytes by a context set up with ANY values of
// zstd's documented decoding parameters: ZSTD_d_windowLogMax, ZSTD_d_format, ZSTD_d_forceIgnoreChecksum,
// ZSTD_d_refMultipleDDicts (with up to two dictionaries of ANY bytes referenced), ZSTD_d_maxBlockSize, and
// ZSTD_DCtx_setMaxWindowSize ("Providing a value beyond bound will either clamp it, or trigger an error"); then one-shot (ZSTD_decompressDCtx, any capacity) or streaming (ZSTD_decompressStream,
// any chunks, the context reset after an error).
//
// Claim (QuickProof.Contract.harness_safe of this program): no execution has undefined behaviour, and every gp_assert
// holds: ZSTD_decompressDCtx returns an error or at most the capacity ("<= dstCapacity"); each streaming call keeps
// "0 <= pos <= size" for its input and output.  The dictionaries' buffers stay alive until the end, as in the other laws:
// zstd keeps the caller's buffer of an empty dictionary although zstd.h says it may be freed.
// Draw order n, bytes, cap (env.c); the rest comes from nondet_u32.
#include <stdlib.h>
#include "quickproof.h"
#ifndef ZSTD_STATIC_LINKING_ONLY
#define ZSTD_STATIC_LINKING_ONLY   /* the experimental parameters */
#endif
#include "zstd.h"

#define SRC_MAX 4096
#define DST_MAX 65536
#define DICT_MAX 512
#define CHUNK_MAX 256
#define CALLS_MAX 512
#define AP_DICTS 2

int main(void)
{
	size_t n = nondet_size(), cap, r, ipos = 0, got = 0;
	unsigned char *src, *dst = NULL;
	unsigned i, calls;
	ZSTD_DCtx *dctx;
	ZSTD_DDict *dd[AP_DICTS];
	unsigned char *dbuf[AP_DICTS];
	static const ZSTD_dParameter ap_params[5] = { ZSTD_d_windowLogMax, ZSTD_d_format, ZSTD_d_forceIgnoreChecksum,
	                                              ZSTD_d_refMultipleDDicts, ZSTD_d_maxBlockSize };
	gp_assume(n <= SRC_MAX);
	src = malloc(n);
	if (src == NULL)
		return 0;                       /* harness out of memory: end the run */
	nondet_bytes(src, n);
	cap = nondet_size();
	gp_assume(cap <= DST_MAX);
	for (i = 0; i < AP_DICTS; i++) {
		dd[i] = NULL;
		dbuf[i] = NULL;
	}
	dctx = ZSTD_createDCtx();
	if (dctx == NULL) {
		free(src);
		return 0;
	}
	/* any parameter values, in any order and number; a refused value is ignored */
	for (i = 0; i < 8; i++) {
		unsigned which = nondet_u32() % 7;
		if (which < 5)
			(void) ZSTD_DCtx_setParameter(dctx, ap_params[which], (int) nondet_u32());
		else if (which == 5)
			(void) ZSTD_DCtx_setMaxWindowSize(dctx, (size_t) nondet_u32() << (nondet_u32() % 2 ? 0 : 8));
		else if (dd[i % AP_DICTS] == NULL) {
			size_t dn = nondet_u32() % (DICT_MAX + 1);
			unsigned char *d;
			free(dbuf[i % AP_DICTS]);       /* a buffer whose dictionary was not created: nothing refers to it */
			d = malloc(dn > 0 ? dn : 1);
			dbuf[i % AP_DICTS] = d;
			if (d != NULL) {
				nondet_bytes(d, dn);
				dd[i % AP_DICTS] = ZSTD_createDDict(d, dn);   /* copies the dictionary */
				if (dd[i % AP_DICTS] != NULL)
					(void) ZSTD_DCtx_refDDict(dctx, dd[i % AP_DICTS]);
			}
		}
	}
	if (nondet_u32() % 2) {
		dst = malloc(cap > 0 ? cap : 1);
		if (dst != NULL) {
			r = ZSTD_decompressDCtx(dctx, dst, cap, src, n);
			gp_assert(ZSTD_isError(r) || r <= cap);
		}
	} else {
		for (calls = 0; calls < CALLS_MAX && got <= cap; calls++) {
			size_t ilen = nondet_u32() % (CHUNK_MAX + 1), olen = nondet_u32() % CHUNK_MAX + 1;
			unsigned char *ib, *ob;
			ZSTD_inBuffer in;
			ZSTD_outBuffer out;
			if (ilen > n - ipos)
				ilen = n - ipos;
			ib = malloc(ilen > 0 ? ilen : 1);
			ob = malloc(olen);
			if (ib == NULL || ob == NULL) {
				free(ib);
				free(ob);
				break;                  /* harness out of memory: end the run */
			}
			for (i = 0; i < ilen; i++)
				ib[i] = src[ipos + i];
			in.src = ib;
			in.size = ilen;
			in.pos = 0;
			out.dst = ob;
			out.size = olen;
			out.pos = 0;
			r = ZSTD_decompressStream(dctx, &out, &in);
			gp_assert(in.pos <= in.size);
			gp_assert(out.pos <= out.size);
			ipos += in.pos;
			got += out.pos;
			free(ib);
			free(ob);
			if (ZSTD_isError(r))
				(void) ZSTD_DCtx_reset(dctx, ZSTD_reset_session_only);   /* zstd.h: reset after an error */
			if (ipos == n && in.pos == 0 && out.pos == 0)
				break;
		}
	}
	ZSTD_freeDCtx(dctx);
	for (i = 0; i < AP_DICTS; i++) {
		ZSTD_freeDDict(dd[i]);
		free(dbuf[i]);
	}
	free(dst);
	free(src);
	return 0;
}
