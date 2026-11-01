// Law valid_dict_api (PROMISES.md: V18-V21; zstd's experimental and deprecated dictionary APIs): ANY dictionaries and
// ANY series of compliant frames written with one of them (harness/writer.h), decoded through:
//   0 ZSTD_d_refMultipleDDicts with 2 or 3 formatted dictionaries of distinct IDs, each referenced with
//     ZSTD_DCtx_refDDict: "At decompression time, the appropriate dictID is selected from the set of DDicts based on
//     the dictID in the frame" (V18); every Zstandard frame of the series carries its dictionary's ID.  One-shot or
//     streaming (upstream's one-shot decoding loads the DDict referenced last before it selects the frame's,
//     changed by F4 in patch/fixes.py);
//   1 ZSTD_DCtx_loadDictionary_advanced(ZSTD_dlm_byCopy or ZSTD_dlm_byRef, ZSTD_dct_auto or ZSTD_dct_rawContent) with
//     a raw-content dictionary ("ZSTD_dct_auto ... rawContent" when it does not start with the magic number) (V19);
//   2 the same with ZSTD_dct_rawContent and a formatted dictionary's bytes, which then are raw content: "ensures
//     dictionary is always loaded as rawContent, even if it starts with ZSTD_MAGIC_DICTIONARY" (V19);
//   3 ZSTD_dct_fullDict with a raw-content dictionary, through ZSTD_DCtx_loadDictionary_advanced or
//     ZSTD_DCtx_refPrefix_advanced: an error, "refuses to load a dictionary if it does not respect Zstandard's
//     specification, starting with ZSTD_MAGIC_DICTIONARY" (V20);
//   4 ZSTD_DCtx_refPrefix_advanced(ZSTD_dct_rawContent or ZSTD_dct_auto), a raw-content prefix and one frame (V19);
//   5 ZSTD_initDStream_usingDict, "equivalent to ZSTD_DCtx_reset(zds, ZSTD_reset_session_only);
//     ZSTD_DCtx_loadDictionary(zds, dict, dictSize)", then streaming; then ZSTD_resetDStream ("reuse decompression
//     parameters from previous init; saves dictionary loading") and the series again (V21);
//   6 ZSTD_initDStream_usingDDict ("ZSTD_DCtx_reset ...; ZSTD_DCtx_refDDict(zds, ddict)"), the same (V21).
//
// Claim (QuickProof.Contract.harness_safe of this program): no execution has undefined behaviour, and every gp_assert
// holds: in mode 3 the load fails; otherwise every byte delivered is the series' content at that position (a one-shot
// success: all of it), and decoding fails only at zstd's documented limits (zlimits.h) or with a one-shot capacity
// below the content.  A setup step that fails (e.g. out of memory) ends the run.  One-shot output and a dictionary
// used by reference are two regions of one allocation [dst | 1 byte | dict] (any_dict explains why).
#include <stdlib.h>
#include "quickproof.h"
#include "writer.h"
#include "zlimits.h"

#define CALLS_MAX 4096
#define VD_DICTS 3

static wdict_t vd_wd[VD_DICTS];
static wdict_t vd_raw;                  /* mode 2: a formatted dictionary's bytes as raw content */
static wseries_t sr;

static size_t vd_chunk(size_t max)
{
	unsigned c = choose(4);
	size_t lim = c == 0 ? 16 : c == 1 ? 512 : c == 2 ? 70000 : max;
	return choose_in(0, lim < max ? lim : max);
}

/* stream the series through ds in any chunks, checking every byte delivered and every return */
static void vd_stream(ZSTD_DStream *ds, const unsigned char *src)
{
	size_t ipos = 0, got = 0, calls, stalled = 0, r, j;
	unsigned k;
	for (calls = 0; calls < CALLS_MAX; calls++) {
		size_t ilen = vd_chunk(sr.n - ipos), olen = 1 + vd_chunk(W_CONTENT_MAX);
		unsigned char *ib = exact_copy(src + ipos, ilen), *ob = malloc(olen);
		ZSTD_inBuffer in;
		ZSTD_outBuffer out;
		if (ib == NULL || ob == NULL) {
			free(ib);
			free(ob);
			break;                      /* harness out of memory: end the run */
		}
		in.src = ib;
		in.size = ilen;
		in.pos = 0;
		out.dst = ob;
		out.size = olen;
		out.pos = 0;
		r = ZSTD_decompressStream(ds, &out, &in);
		gp_assert(in.pos <= in.size);
		gp_assert(out.pos <= out.size);
		for (j = 0; j < out.pos; j++) {
			gp_assert(got + j < sr.content_n);
			gp_assert(ob[j] == sr.content[got + j]);
		}
		got += out.pos;
		ipos += in.pos;
		free(ib);
		free(ob);
		if (ZSTD_isError(r)) {
			gp_assert(!within_stream(&sr) || ZSTD_getErrorCode(r) == ZSTD_error_memory_allocation
			          || stall_error(ZSTD_getErrorCode(r), stalled, &in, &out, 0));
			break;
		}
		stalled = in.pos == 0 && out.pos == 0 ? stalled + 1 : 0;
		if (r == 0) {
			int at_end = 0;
			for (k = 0; k < sr.nframes; k++)
				if (sr.f[k].start + sr.f[k].size == ipos && got == sr.f[k].cstart + sr.f[k].csize)
					at_end = 1;
			gp_assert(at_end);
			if (ipos == sr.n)
				break;
		}
	}
}

int main(void)
{
	unsigned mode = choose(7), nd = 1, which = 0, i, k;
	size_t cap = 0, r, j, dn;
	const wdict_t *wd;
	unsigned char *src, *buf, *dst, *dict;
	ZSTD_DCtx *dctx;
	ZSTD_DDict *dd[VD_DICTS];
	int fail = 0;
	for (i = 0; i < VD_DICTS; i++)
		dd[i] = NULL;
	if (mode == 0)
		nd = 2 + choose(VD_DICTS - 1);
	for (i = 0; i < nd; i++) {
		w_dict(&vd_wd[i]);
		if (mode == 0) {
			gp_assume(vd_wd[i].formatted);
			for (k = 0; k < i; k++)
				gp_assume(vd_wd[i].id != vd_wd[k].id);
		}
	}
	if (mode == 0)
		which = choose(nd);
	wd = &vd_wd[which];
	if (mode == 1 || mode == 3 || mode == 4)
		gp_assume(!wd->formatted);
	if (mode == 2) {
		gp_assume(wd->formatted && wd->n <= W_DICT_MAX);
		vd_raw.formatted = 0;
		vd_raw.id = 0;
		vd_raw.content = wd->bytes;
		vd_raw.content_n = wd->n;
		vd_raw.st.have_huf = 0;
		vd_raw.st.have_tab = 0;
		vd_raw.st.rep[0] = 1;
		vd_raw.st.rep[1] = 4;
		vd_raw.st.rep[2] = 8;
		w_series(&sr, &vd_raw);
	} else {
		w_series(&sr, wd);
	}
	if (mode == 0)
		for (k = 0; k < sr.nframes; k++)
			gp_assume(sr.f[k].skippable || (sr.f[k].did_size != 0 && sr.f[k].did == wd->id));
	if (mode == 4)
		gp_assume(sr.nframes == 1 && !sr.f[0].skippable);
	dn = wd->n;
	if (mode != 5 && mode != 6)
		cap = choose_in(0, sr.content_n + 16);
	src = exact_copy(sr.bytes, sr.n);
	buf = malloc(cap + 1 + dn);
	dctx = ZSTD_createDCtx();
	dst = buf;
	dict = NULL;
	if (buf != NULL)
		dict = buf + cap + 1;           /* not on NULL: NULL + n is undefined (C11 6.5.6p8) */
	if (src == NULL || buf == NULL || dctx == NULL) {
		free(src);
		free(buf);
		ZSTD_freeDCtx(dctx);
		return 0;                       /* out of memory: end the run */
	}
	for (j = 0; j < dn; j++)
		dict[j] = wd->bytes[j];
	/* set up the dictionary */
	if (mode == 0) {
		r = ZSTD_DCtx_setParameter(dctx, ZSTD_d_refMultipleDDicts, ZSTD_rmd_refMultipleDDicts);
		gp_assert(!ZSTD_isError(r));    /* a ZSTD_refMultipleDDicts_e value, on a new context */
		for (i = 0; i < nd && !fail; i++) {
			dd[i] = ZSTD_createDDict(vd_wd[i].bytes, vd_wd[i].n);
			if (dd[i] == NULL || ZSTD_isError(ZSTD_DCtx_refDDict(dctx, dd[i])))
				fail = 1;
		}
	} else if (mode == 1 || mode == 2) {
		ZSTD_dictLoadMethod_e m = choose(2) ? ZSTD_dlm_byRef : ZSTD_dlm_byCopy;
		ZSTD_dictContentType_e t = (mode == 2 || choose(2)) ? ZSTD_dct_rawContent : ZSTD_dct_auto;
		fail = ZSTD_isError(ZSTD_DCtx_loadDictionary_advanced(dctx, dict, dn, m, t));
	} else if (mode == 3) {
		if (choose(2))
			r = ZSTD_DCtx_loadDictionary_advanced(dctx, dict, dn, choose(2) ? ZSTD_dlm_byRef : ZSTD_dlm_byCopy,
			                                      ZSTD_dct_fullDict);
		else
			r = ZSTD_DCtx_refPrefix_advanced(dctx, dict, dn, ZSTD_dct_fullDict);
		gp_assert(ZSTD_isError(r));
		fail = 1;                       /* nothing to decode */
	} else if (mode == 4) {
		fail = ZSTD_isError(ZSTD_DCtx_refPrefix_advanced(dctx, dict, dn,
		                                                 choose(2) ? ZSTD_dct_rawContent : ZSTD_dct_auto));
	} else if (mode == 5) {
		fail = ZSTD_isError(ZSTD_initDStream_usingDict(dctx, dict, dn));
	} else {
		dd[0] = ZSTD_createDDict(dict, dn);
		fail = dd[0] == NULL || ZSTD_isError(ZSTD_initDStream_usingDDict(dctx, dd[0]));
	}
	if (!fail) {
		if (mode == 5 || mode == 6) {
			vd_stream(dctx, src);
			if (!ZSTD_isError(ZSTD_resetDStream(dctx)))
				vd_stream(dctx, src);
		} else if (mode == 0 && choose(2)) {
			vd_stream(dctx, src);
		} else {
			r = ZSTD_decompressDCtx(dctx, dst, cap, src, sr.n);
			if (!ZSTD_isError(r)) {
				gp_assert(r == sr.content_n);
				for (j = 0; j < r; j++)
					gp_assert(dst[j] == sr.content[j]);
			} else if (cap >= sr.content_n && within_oneshot(&sr)) {
				gp_assert(ZSTD_getErrorCode(r) == ZSTD_error_memory_allocation);
			}
		}
	}
	ZSTD_freeDCtx(dctx);
	for (i = 0; i < VD_DICTS; i++)
		ZSTD_freeDDict(dd[i]);
	free(src);
	free(buf);
	return 0;
}
