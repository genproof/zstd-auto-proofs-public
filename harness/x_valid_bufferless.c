// Law valid_bufferless (PROMISES.md: V22; zstd's experimental "Buffer-less streaming decompression (synchronous
// mode)"): ANY series of compliant frames (harness/writer.h), with no dictionary, ANY dictionary through
// ZSTD_decompressBegin_usingDict, or the same through a ZSTD_DDict and ZSTD_decompressBegin_usingDDict, decoded frame
// by frame: ZSTD_decompressBegin*, then "ZSTD_nextSrcSizeToDecompress() and ZSTD_decompressContinue() alternatively",
// each call given exactly the requested number of bytes, the output of every frame right after the previous one in one
// buffer that holds the series' content ("decompresses each block next to previous one").
//
// Claim (QuickProof.Contract.harness_safe of this program): no execution has undefined behaviour, and every gp_assert
// holds: ZSTD_nextSrcSizeToDecompress asks for no more than what remains of the frame; ZSTD_decompressContinue returns
// "the number of bytes regenerated within 'dst' (necessarily <= dstCapacity)", those bytes being the series' content
// at that position, and 0 throughout a skippable frame ("For skippable frames ZSTD_decompressContinue() always
// returns 0"); "A frame is fully decoded when ZSTD_nextSrcSizeToDecompress() returns zero", exactly at its end with
// all its content regenerated; ZSTD_nextInputType returns one of its enumerators.  Decoding fails only for a frame
// beyond zstd's window range (zlimits.h).  A ZSTD_decompressBegin* that fails (e.g. out of memory) ends the run.
// The output and a dictionary used by reference are two regions of one allocation [dst | 1 byte | dict] (any_dict
// explains why).
#include <stdlib.h>
#include "quickproof.h"
#include "writer.h"
#include "zlimits.h"

static wdict_t vb_wd;
static wseries_t sr;

int main(void)
{
	unsigned mode = choose(3), k;
	size_t cap, dn = 0, ipos = 0, pos = 0, r, j;
	unsigned char *src, *buf, *dst, *dict;
	ZSTD_DCtx *dctx;
	ZSTD_DDict *ddict = NULL;
	int stop = 0;
	if (mode != 0) {
		w_dict(&vb_wd);
		dn = vb_wd.n;
		w_series(&sr, &vb_wd);
	} else {
		w_series(&sr, 0);
	}
	cap = sr.content_n;
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
		dict[j] = vb_wd.bytes[j];
	if (mode == 2) {
		ddict = ZSTD_createDDict(dict, dn);
		if (ddict == NULL)
			stop = 1;
	}
	for (k = 0; k < sr.nframes && !stop; k++) {
		const winfo_t *f = &sr.f[k];
		size_t end = f->start + f->size, cend = f->cstart + f->csize;
		r = mode == 0 ? ZSTD_decompressBegin(dctx) : mode == 1 ? ZSTD_decompressBegin_usingDict(dctx, dict, dn)
		    : ZSTD_decompressBegin_usingDDict(dctx, ddict);
		if (ZSTD_isError(r))
			break;                      /* no claim */
		gp_assert(ipos == f->start && pos == f->cstart);
		for (;;) {
			size_t want = ZSTD_nextSrcSizeToDecompress(dctx);
			ZSTD_nextInputType_e t = ZSTD_nextInputType(dctx);
			unsigned char *ib;
			gp_assert(t == ZSTDnit_frameHeader || t == ZSTDnit_blockHeader || t == ZSTDnit_block
			          || t == ZSTDnit_lastBlock || t == ZSTDnit_checksum || t == ZSTDnit_skippableFrame);
			if (want == 0) {
				gp_assert(ipos == end && pos == cend);
				break;                  /* the frame is fully decoded */
			}
			gp_assert(want <= end - ipos);
			ib = exact_copy(src + ipos, want);
			if (ib == NULL) {
				stop = 1;               /* harness out of memory: end the run */
				break;
			}
			r = ZSTD_decompressContinue(dctx, dst + pos, cap - pos, ib, want);
			free(ib);
			if (ZSTD_isError(r)) {
				gp_assert(!within_oneshot(&sr));
				stop = 1;
				break;
			}
			gp_assert(r <= cap - pos);
			if (f->skippable)
				gp_assert(r == 0);
			for (j = 0; j < r; j++)
				gp_assert(dst[pos + j] == sr.content[pos + j]);
			pos += r;
			ipos += want;
		}
	}
	ZSTD_freeDDict(ddict);
	ZSTD_freeDCtx(dctx);
	free(src);
	free(buf);
	return 0;
}
