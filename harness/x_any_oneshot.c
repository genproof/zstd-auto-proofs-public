// Law any_oneshot (PROMISES.md: S1, S3, S6, V7): one-shot decompression of ANY bytes into ANY capacity.
//
// Claim (QuickProof.Contract.harness_safe of this program): no execution has undefined behaviour, and every gp_assert
// holds: ZSTD_decompress, and ZSTD_decompressDCtx on a context used before (also after an error: "reset is implied
// for operations starting some new decompression job"), return an error or "the number of bytes decompressed into
// `dst` (<= `dstCapacity`)"; ZSTD_freeDCtx accepts NULL.  Buffers have exactly the size of their contents; src and
// dst are separate objects.  Draw order n, bytes, cap, twice (env.c hands out real frames this way).
#include <stdlib.h>
#include "quickproof.h"
#include "zstd.h"

#define SRC_MAX 4096
#define DST_MAX 65536

int main(void)
{
	unsigned char *src[2], *dst[2];
	size_t n[2], cap[2], r;
	unsigned i;
	ZSTD_DCtx *dctx;
	for (i = 0; i < 2; i++) {
		n[i] = nondet_size();
		gp_assume(n[i] <= SRC_MAX);
		src[i] = malloc(n[i]);
		if (src[i] == NULL)
			return 0;                   /* harness out of memory: end the run */
		nondet_bytes(src[i], n[i]);
		cap[i] = nondet_size();
		gp_assume(cap[i] <= DST_MAX);
		dst[i] = malloc(cap[i]);
		if (dst[i] == NULL)
			return 0;
	}
	r = ZSTD_decompress(dst[0], cap[0], src[0], n[0]);
	if (!ZSTD_isError(r))
		gp_assert(r <= cap[0]);
	dctx = ZSTD_createDCtx();
	if (dctx != NULL) {
		for (i = 0; i < 2; i++) {
			r = ZSTD_decompressDCtx(dctx, dst[i], cap[i], src[i], n[i]);
			if (!ZSTD_isError(r))
				gp_assert(r <= cap[i]);
		}
	}
	ZSTD_freeDCtx(dctx);
	ZSTD_freeDCtx(NULL);
	for (i = 0; i < 2; i++) {
		free(src[i]);
		free(dst[i]);
	}
	return 0;
}
