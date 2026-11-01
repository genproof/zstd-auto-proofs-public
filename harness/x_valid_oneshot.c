// Law valid_oneshot (PROMISES.md: V1-V4, V7): ANY series of compliant frames (harness/writer.h: Zstandard frames of
// every form and skippable frames), decoded in one shot into ANY capacity.
//
// Claim (QuickProof.Contract.harness_safe of this program): no execution has undefined behaviour, and every gp_assert
// holds: a success returns exactly the series' content ("The result will be the concatenation of all decompressed
// frames, back to back"; "skippable frames need just be skipped"); with a capacity that holds the content it succeeds
// ("must decode any compliant frame"), unless a frame's window is beyond zstd's range or a context cannot be
// allocated (zlimits.h).  The decoder is ZSTD_decompress, or ZSTD_decompressDCtx on a context that has already decoded
// other bytes ("Same as ZSTD_decompress()").  src and dst are separate objects of exactly their sizes.
#include <stdlib.h>
#include "quickproof.h"
#include "writer.h"
#include "zlimits.h"

#define OTHER_MAX 4096

static wseries_t sr;

int main(void)
{
	size_t cap, r, i;
	unsigned char *src, *dst;
	ZSTD_DCtx *dctx = NULL;
	w_series(&sr, 0);
	cap = choose_in(0, sr.content_n + 16);
	src = exact_copy(sr.bytes, sr.n);
	dst = malloc(cap > 0 ? cap : 1);
	if (src == NULL || dst == NULL) {
		free(src);
		free(dst);
		return 0;                       /* harness out of memory: end the run */
	}
	if (choose(2)) {
		r = ZSTD_decompress(dst, cap, src, sr.n);
	} else {
		size_t m = choose_in(0, OTHER_MAX);
		unsigned char *other = malloc(m > 0 ? m : 1);
		dctx = ZSTD_createDCtx();
		if (other == NULL || dctx == NULL) {
			ZSTD_freeDCtx(dctx);
			free(other);
			free(src);
			free(dst);
			return 0;
		}
		nondet_bytes(other, m);
		(void) ZSTD_decompressDCtx(dctx, dst, cap, other, m);   /* any earlier use, error or not */
		free(other);
		r = ZSTD_decompressDCtx(dctx, dst, cap, src, sr.n);
	}
	if (!ZSTD_isError(r)) {
		gp_assert(r == sr.content_n);
		for (i = 0; i < r; i++)
			gp_assert(dst[i] == sr.content[i]);
	} else if (cap >= sr.content_n && within_oneshot(&sr)) {
		gp_assert(ZSTD_getErrorCode(r) == ZSTD_error_memory_allocation);
	}
	ZSTD_freeDCtx(dctx);
	free(src);
	free(dst);
	return 0;
}
