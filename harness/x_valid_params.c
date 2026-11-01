// Law valid_params (PROMISES.md: V14-V17): ANY series of compliant frames (harness/writer.h) decoded under one of
// zstd's documented decoding parameters, one-shot (ZSTD_decompressDCtx, any capacity) or streaming
// (ZSTD_decompressStream, any input and output chunks):
//   0 ZSTD_d_forceIgnoreChecksum = ZSTD_d_ignoreChecksum, with the Content_Checksum of any frames replaced by any value:
//     "Tells the decompressor to skip checksum validation during decompression, regardless of whether checksumming
//     was specified during compression" (V14);
//   1 a window limit, ZSTD_d_windowLogMax ("Select a size limit (in power of 2) beyond which the streaming API will
//     refuse to allocate memory buffer"; "value 0 means use default maximum windowLog") or ZSTD_DCtx_setMaxWindowSize
//     ("Refuses allocating internal buffers for frames requiring a window size larger than provided limit"): frames
//     within the limit decode; one-shot decoding ignores it ("only useful in streaming mode, since no internal buffer
//     is allocated in single-pass mode") (V15);
//   2 ZSTD_d_maxBlockSize ("reject blocks whose content size is larger than the configured maxBlockSize"; "setting to
//     0 will set to the default", ZSTD_BLOCKSIZE_MAX), a lower Block_Maximum_Size, which the format applies "to both
//     the decompressed size and the compressed size of any block in the frame" (its Block_Content is the compressed
//     bytes): a series whose frames' contents and whole sizes in bytes fit the limit, so do their blocks' sizes, both
//     (V16).  Other series are out of this law (zstd.h promises their rejection, not encoded here; any_params covers
//     any bytes under any maxBlockSize);
//   3 ZSTD_d_format = ZSTD_f_zstd1_magicless, or ZSTD_DCtx_setFormat: one Zstandard frame without its magic number,
//     "Variant of zstd frame format, without initial 4-bytes magic number" (V17); and ZSTD_getFrameHeader_advanced
//     with that format ("same as ZSTD_getFrameHeader(), with added capability to select a format") reads the header
//     the frame was written with, 4 bytes shorter (or an error when its window is beyond zstd's range, zlimits.h).
//
// Claim (QuickProof.Contract.harness_safe of this program): no execution has undefined behaviour, and every gp_assert
// holds: every byte delivered is the series' content at that position (a one-shot success delivers all of it);
// decoding fails only at zstd's documented limits (zlimits.h: the window range, memory, the streaming busy-loop guard,
// and the streaming default window limit or, in mode 1, the limit set), or one-shot with a capacity below the
// content; "0 <= pos <= size"; a streaming call returns 0
// only at the end of a frame with all its content delivered.  A parameter zstd refuses to set ends the run (zstd.h
// does not say it cannot); a value zstd.h allows (a ZSTD_forceIgnoreChecksum_e or ZSTD_format_e value, windowLogMax 0,
// maxBlockSize 0 or "between 1KB and ZSTD_BLOCKSIZE_MAX") is set successfully on a new context.
#include <stdlib.h>
#include "quickproof.h"
#include "writer.h"
#include "zlimits.h"

#define CALLS_MAX 4096

static wseries_t sr;

static size_t vp_chunk(size_t max)
{
	unsigned c = choose(4);
	size_t lim = c == 0 ? 16 : c == 1 ? 512 : c == 2 ? 70000 : max;
	return choose_in(0, lim < max ? lim : max);
}

/* true iff every Zstandard frame's window is at most lim (single-segment: Window_Size = content size) */
static int vp_windows_within(unsigned long long lim)
{
	unsigned k;
	for (k = 0; k < sr.nframes; k++)
		if (!sr.f[k].skippable && sr.f[k].window > lim)
			return 0;
	return 1;
}

/* true iff every Zstandard frame's content and size in bytes are at most lim: then so are each of its blocks' content
 * and Block_Size (smaller than the frame) */
static int vp_blocks_within(unsigned long long lim)
{
	unsigned k;
	for (k = 0; k < sr.nframes; k++)
		if (!sr.f[k].skippable && (sr.f[k].csize > lim || sr.f[k].size > lim))
			return 0;
	return 1;
}

int main(void)
{
	unsigned mode = choose(4), k, j;
	unsigned long long wlim = 1ULL << ZSTD_WINDOWLOG_LIMIT_DEFAULT, blim = ZSTD_BLOCKSIZE_MAX;
	size_t base = 0, n, r, i;
	int documented = 1;                 /* the value set is one zstd.h allows: setting it succeeds */
	unsigned char *src;
	ZSTD_DCtx *dctx;
	w_series(&sr, 0);
	if (mode == 0) {
		for (k = 0; k < sr.nframes; k++)
			if (!sr.f[k].skippable && sr.f[k].checksum && choose(2))
				for (j = 0; j < 4; j++)
					sr.bytes[sr.f[k].start + sr.f[k].size - 4 + j] = (unsigned char) choose(256);
	}
	if (mode == 3) {
		gp_assume(sr.nframes == 1 && !sr.f[0].skippable);
		base = 4;                       /* the frame without its magic number */
	}
	n = sr.n - base;
	src = exact_copy(sr.bytes + base, n);
	dctx = ZSTD_createDCtx();
	if (src == NULL || dctx == NULL) {
		free(src);
		ZSTD_freeDCtx(dctx);
		return 0;                       /* out of memory: end the run */
	}
	if (mode == 0) {
		r = ZSTD_DCtx_setParameter(dctx, ZSTD_d_forceIgnoreChecksum, ZSTD_d_ignoreChecksum);
	} else if (mode == 1) {
		if (choose(2)) {
			unsigned wl = choose(2) ? 0 : (unsigned) choose_in(ZSTD_WINDOWLOG_MIN, ZSTD_WINDOWLOG_MAX);
			if (wl != 0) {
				wlim = 1ULL << wl;
				documented = 0;             /* bounds only through ZSTD_dParam_getBounds */
			}
			r = ZSTD_DCtx_setParameter(dctx, ZSTD_d_windowLogMax, (int) wl);
		} else {
			size_t m = choose_in((size_t) 1 << ZSTD_WINDOWLOG_MIN, (size_t) 1 << ZSTD_WINDOWLOG_MAX);
			wlim = m;
			documented = 0;
			r = ZSTD_DCtx_setMaxWindowSize(dctx, m);
		}
	} else if (mode == 2) {
		unsigned b = choose(2) ? 0 : (unsigned) choose_in(1024, ZSTD_BLOCKSIZE_MAX);
		if (b != 0)
			blim = b;
		r = ZSTD_DCtx_setParameter(dctx, ZSTD_d_maxBlockSize, (int) b);
		gp_assume(vp_blocks_within(blim));
	} else {
		r = choose(2) ? ZSTD_DCtx_setParameter(dctx, ZSTD_d_format, ZSTD_f_zstd1_magicless)
		    : ZSTD_DCtx_setFormat(dctx, ZSTD_f_zstd1_magicless);
	}
	gp_assert(!documented || !ZSTD_isError(r));
	if (ZSTD_isError(r)) {
		free(src);
		ZSTD_freeDCtx(dctx);
		return 0;                       /* the parameter was not set: no claim */
	}
	if (mode == 3) {
		ZSTD_FrameHeader zfh;
		const winfo_t *f = &sr.f[0];
		int big = !f->single && f->window_log > ZSTD_WINDOWLOG_MAX;   /* beyond zstd's range (zlimits.h) */
		r = ZSTD_getFrameHeader_advanced(&zfh, src, n, ZSTD_f_zstd1_magicless);
		gp_assert(r == 0 || (big && ZSTD_isError(r)));
		if (r == 0) {
			gp_assert(zfh.frameType == ZSTD_frame);
			gp_assert(zfh.frameContentSize == (f->fcs_present ? f->fcs : ZSTD_CONTENTSIZE_UNKNOWN));
			gp_assert(zfh.windowSize == f->window);
			gp_assert(zfh.headerSize == f->hsize - 4);
			gp_assert(zfh.dictID == f->did);
			gp_assert(zfh.checksumFlag == f->checksum);
		}
	}
	if (choose(2)) {
		/* one-shot */
		size_t cap = choose_in(0, sr.content_n + 16);
		unsigned char *dst = malloc(cap > 0 ? cap : 1);
		if (dst != NULL) {
			r = ZSTD_decompressDCtx(dctx, dst, cap, src, n);
			if (!ZSTD_isError(r)) {
				gp_assert(r == sr.content_n);
				for (i = 0; i < r; i++)
					gp_assert(dst[i] == sr.content[i]);
			} else if (cap >= sr.content_n && within_oneshot(&sr)) {
				gp_assert(ZSTD_getErrorCode(r) == ZSTD_error_memory_allocation);
			}
			free(dst);
		}
	} else {
		/* streaming */
		size_t ipos = 0, got = 0, calls, stalled = 0;
		int within = within_oneshot(&sr) && vp_windows_within(wlim);
		for (calls = 0; calls < CALLS_MAX; calls++) {
			size_t ilen = vp_chunk(n - ipos), olen = 1 + vp_chunk(W_CONTENT_MAX);
			unsigned char *ib = exact_copy(src + ipos, ilen), *ob = malloc(olen);
			ZSTD_inBuffer in;
			ZSTD_outBuffer out;
			if (ib == NULL || ob == NULL) {
				free(ib);
				free(ob);
				break;                  /* harness out of memory: end the run */
			}
			in.src = ib;
			in.size = ilen;
			in.pos = 0;
			out.dst = ob;
			out.size = olen;
			out.pos = 0;
			r = ZSTD_decompressStream(dctx, &out, &in);
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
				gp_assert(!within || ZSTD_getErrorCode(r) == ZSTD_error_memory_allocation
				          || stall_error(ZSTD_getErrorCode(r), stalled, &in, &out, 0));
				break;
			}
			stalled = in.pos == 0 && out.pos == 0 ? stalled + 1 : 0;
			if (r == 0) {
				int at_end = 0;
				for (k = 0; k < sr.nframes; k++)
					if (sr.f[k].start + sr.f[k].size - base == ipos && got == sr.f[k].cstart + sr.f[k].csize)
						at_end = 1;
				gp_assert(at_end);
				if (ipos == n)
					break;
			}
		}
	}
	ZSTD_freeDCtx(dctx);
	free(src);
	return 0;
}
