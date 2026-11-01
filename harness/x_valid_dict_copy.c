// Law valid_dict_copy (PROMISES.md: V8, V9, V1-V4): ANY dictionary (harness/writer.h) and ANY series of compliant frames
// written with it, decoded through the dictionary APIs that copy the dictionary: 1 ZSTD_createDDict +
// ZSTD_decompress_usingDDict; 2 ZSTD_DCtx_loadDictionary, sticky ("they remain valid when same context is reused"): the
// series is decoded twice; 3 ZSTD_createDDict + ZSTD_DCtx_refDDict.
//
// Claim (QuickProof.Contract.harness_safe of this program): no execution has undefined behaviour, and every gp_assert
// holds: a success returns exactly the series' content; with a capacity that holds it, decoding succeeds unless a
// frame's window is beyond zstd's range or memory cannot be allocated (zlimits.h).
// zstd compares the output pointer with the end of its own copy of the dictionary, which CompCert's semantics
// cannot do; the patch's VST layer skips that comparison for a copied dictionary (patch/GENPROOF-PATCH.md, gpDictCopy).
#include <stdlib.h>
#include "quickproof.h"
#include "writer.h"
#include "zlimits.h"

static wdict_t wd;
static wseries_t sr;

int main(void)
{
	size_t cap, r, i;
	unsigned char *src, *dst, *dict;
	unsigned api = 1 + choose(3), rounds, k;
	ZSTD_DCtx *dctx;
	ZSTD_DDict *ddict = NULL;
	w_dict(&wd);
	w_series(&sr, &wd);
	cap = choose_in(0, sr.content_n + 16);
	src = exact_copy(sr.bytes, sr.n);
	dict = exact_copy(wd.bytes, wd.n);
	dst = malloc(cap > 0 ? cap : 1);
	dctx = ZSTD_createDCtx();
	rounds = (src != NULL && dict != NULL && dst != NULL && dctx != NULL) ? (api == 2 ? 2 : 1) : 0;
	if (rounds > 0 && api != 2) {
		ddict = ZSTD_createDDict(dict, wd.n);
		if (ddict == NULL)
			rounds = 0;                 /* out of memory: end the run */
	}
	for (k = 0; k < rounds; k++) {
		if (api == 1) {
			r = ZSTD_decompress_usingDDict(dctx, dst, cap, src, sr.n, ddict);
		} else {
			r = 0;
			if (k == 0) {
				r = api == 2 ? ZSTD_DCtx_loadDictionary(dctx, dict, wd.n) : ZSTD_DCtx_refDDict(dctx, ddict);
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
	free(dict);
	free(dst);
	return 0;
}
