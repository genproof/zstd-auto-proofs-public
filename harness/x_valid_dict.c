// Law valid_dict (PROMISES.md: V8, V9, V1-V4): ANY dictionary (harness/writer.h: raw content, or formatted with entropy
// tables and repeat offsets) and ANY series of compliant frames written with it, decoded through the dictionary APIs
// that use the caller's dictionary by reference.
//
// Claim (QuickProof.Contract.harness_safe of this program): no execution has undefined behaviour, and every gp_assert
// holds: a success returns exactly the series' content; with a capacity that holds it, decoding succeeds unless a
// frame's window is beyond zstd's range or memory cannot be allocated (zlimits.h).  The APIs: 0
// ZSTD_decompress_usingDict; 1 ZSTD_createDDict_byReference + ZSTD_decompress_usingDDict; 2
// ZSTD_DCtx_loadDictionary_byReference, sticky ("they remain valid when same context is reused"): the series is decoded
// twice; 3 ZSTD_createDDict_byReference + ZSTD_DCtx_refDDict; 4 ZSTD_DCtx_refPrefix, "only used once" and "treated as
// raw content": a raw dictionary and a single frame.  The output and the dictionary are two regions of one allocation
// [dst | 1 byte | dict] (any_dict explains why); the APIs that copy the dictionary are in valid_dict_copy.
#include <stdlib.h>
#include "quickproof.h"
#include "writer.h"
#include "zlimits.h"

static wdict_t wd;
static wseries_t sr;

int main(void)
{
	size_t cap, r, i;
	unsigned char *src, *buf, *dst, *dict;
	unsigned api = choose(5), rounds, k;
	ZSTD_DCtx *dctx;
	ZSTD_DDict *ddict = NULL;
	w_dict(&wd);
	w_series(&sr, &wd);
	if (api == 4)
		gp_assume(!wd.formatted && sr.nframes == 1 && !sr.f[0].skippable);
	cap = choose_in(0, sr.content_n + 16);
	src = exact_copy(sr.bytes, sr.n);
	buf = malloc(cap + 1 + wd.n);
	dctx = ZSTD_createDCtx();
	rounds = (src != NULL && buf != NULL && dctx != NULL) ? (api == 2 ? 2 : 1) : 0;
	dst = buf;
	dict = NULL;
	if (buf != NULL)
		dict = buf + cap + 1;     /* not on NULL: NULL + n is undefined (C11 6.5.6p8) */
	if (rounds > 0) {
		for (i = 0; i < wd.n; i++)
			dict[i] = wd.bytes[i];
		if (api == 1 || api == 3) {
			ddict = ZSTD_createDDict_byReference(dict, wd.n);
			if (ddict == NULL)
				rounds = 0;             /* out of memory: end the run */
		}
	}
	for (k = 0; k < rounds; k++) {
		if (api == 0) {
			r = ZSTD_decompress_usingDict(dctx, dst, cap, src, sr.n, dict, wd.n);
		} else if (api == 1) {
			r = ZSTD_decompress_usingDDict(dctx, dst, cap, src, sr.n, ddict);
		} else {
			r = 0;
			if (k == 0) {
				r = api == 2 ? ZSTD_DCtx_loadDictionary_byReference(dctx, dict, wd.n)
				    : api == 3 ? ZSTD_DCtx_refDDict(dctx, ddict) : ZSTD_DCtx_refPrefix(dctx, dict, wd.n);
				if (ZSTD_isError(r))
					rounds = 1;         /* no dictionary loaded (e.g. out of memory): no second round */
			}
			if (!ZSTD_isError(r))
				r = ZSTD_decompressDCtx(dctx, dst, cap, src, sr.n);
		}
		if (!ZSTD_isError(r)) {
			gp_assert(r == sr.content_n);
			for (i = 0; i < r; i++)
				gp_assert(dst[i] == sr.content[i]);
		} else if (cap >= sr.content_n && within_oneshot(&sr)) {
			gp_assert(ZSTD_getErrorCode(r) == ZSTD_error_memory_allocation);
		}
	}
	ZSTD_freeDDict(ddict);
	ZSTD_freeDCtx(dctx);
	free(src);
	free(buf);
	return 0;
}
