// Law valid_info (PROMISES.md: I1-I6): the frame-inspection functions on ANY series of compliant frames, with or
// without ANY dictionary (harness/writer.h).
//
// Claim (QuickProof.Contract.harness_safe of this program): no execution has undefined behaviour, and every gp_assert
// holds; at the start of each frame of the series (zstd.h):
//   ZSTD_findFrameCompressedSize = the frame's size (a skippable frame: "its content size + 8 bytes");
//   ZSTD_getFrameContentSize = its Frame_Content_Size, or ZSTD_CONTENTSIZE_UNKNOWN when absent; 0 for a skippable frame;
//   ZSTD_getDictID_fromFrame = its Dictionary_ID (0 when absent, and for a skippable frame);
//   ZSTD_isFrame = 1; ZSTD_isSkippableFrame = whether it is skippable;
//   ZSTD_getFrameHeader = 0, with the frame's frameContentSize, windowSize, blockSizeMax, frameType, headerSize,
//     dictID and checksumFlag (a skippable frame: its content size, type and "skippable magic variant");
//   ZSTD_frameHeaderSize = its header's size (Zstandard frames);
//   ZSTD_readSkippableFrame = its user data and magic variant, or an error when dstCapacity cannot hold them;
// for the whole series: ZSTD_findDecompressedSize = the content size when every Zstandard frame declares its size, else
// ZSTD_CONTENTSIZE_UNKNOWN; ZSTD_decompressBound = the sum per frame of the declared size, or "# blocks * min(128 KB,
// Window_Size)"; and ZSTD_getDictID_fromDict = the dictionary's ID (0 for a raw-content dictionary).  A frame whose
// window is beyond zstd's range may give an error instead (zlimits.h).
#include <stdlib.h>
#include "quickproof.h"
#include "writer.h"
#include "zlimits.h"

static wdict_t wd;
static wseries_t sr;

int main(void)
{
	int withdict = choose(2), anybig = 0, allfcs = 1;
	unsigned char *src, *dst;
	size_t cap, r, i;
	unsigned long long bound = 0;
	unsigned k;
	if (withdict) {
		w_dict(&wd);
		w_series(&sr, &wd);
		gp_assert(ZSTD_getDictID_fromDict(wd.bytes, wd.n) == (wd.formatted ? wd.id : 0));
	} else {
		w_series(&sr, 0);
	}
	cap = choose_in(0, W_SKIP_MAX + 4);
	src = exact_copy(sr.bytes, sr.n);
	dst = malloc(cap > 0 ? cap : 1);
	if (src == NULL || dst == NULL) {
		free(src);
		free(dst);
		return 0;                       /* harness out of memory: end the run */
	}
	for (k = 0; k < sr.nframes; k++) {
		const winfo_t *f = &sr.f[k];
		const unsigned char *p = src + f->start;
		size_t rest = sr.n - f->start;
		int big = !f->skippable && !f->single && f->window_log > ZSTD_WINDOWLOG_MAX;
		unsigned long long c;
		ZSTD_FrameHeader zfh;
		anybig |= big;
		if (!f->skippable) {
			if (f->fcs_present)
				bound += f->fcs;
			else {
				bound += (unsigned long long) f->blocks * (f->window < (1ULL << 17) ? f->window : (1ULL << 17));
				allfcs = 0;
			}
		}
		r = ZSTD_findFrameCompressedSize(p, rest);
		gp_assert(r == f->size || (big && ZSTD_isError(r)));
		c = ZSTD_getFrameContentSize(p, rest);
		if (f->skippable)
			gp_assert(c == 0);
		else
			gp_assert(c == (f->fcs_present ? f->fcs : ZSTD_CONTENTSIZE_UNKNOWN) || (big && c == ZSTD_CONTENTSIZE_ERROR));
		gp_assert(ZSTD_getDictID_fromFrame(p, rest) == (f->skippable ? 0 : f->did) || big);
		gp_assert(ZSTD_isFrame(p, rest) == 1);
		gp_assert(ZSTD_isSkippableFrame(p, rest) == f->skippable);
		r = ZSTD_getFrameHeader(&zfh, p, rest);
		gp_assert(r == 0 || (big && ZSTD_isError(r)));
		if (r == 0 && f->skippable) {
			gp_assert(zfh.frameType == ZSTD_skippableFrame);
			gp_assert(zfh.frameContentSize == f->skip_n);
			gp_assert(zfh.dictID == f->variant);
		} else if (r == 0) {
			gp_assert(zfh.frameType == ZSTD_frame);
			gp_assert(zfh.frameContentSize == (f->fcs_present ? f->fcs : ZSTD_CONTENTSIZE_UNKNOWN));
			gp_assert(zfh.windowSize == f->window);
			gp_assert(zfh.blockSizeMax == (f->window < (1ULL << 17) ? f->window : (1ULL << 17)));
			gp_assert(zfh.headerSize == f->hsize);
			gp_assert(zfh.dictID == f->did);
			gp_assert(zfh.checksumFlag == f->checksum);
		}
		if (!f->skippable)
			gp_assert(ZSTD_frameHeaderSize(p, rest) == f->hsize);
		if (f->skippable) {
			unsigned v = 0;
			r = ZSTD_readSkippableFrame(dst, cap, &v, p, rest);
			if (cap >= f->skip_n) {
				gp_assert(r == f->skip_n);
				gp_assert(v == f->variant);
				for (i = 0; i < r; i++)
					gp_assert(dst[i] == p[8 + i]);
			} else {
				gp_assert(ZSTD_isError(r));
			}
		}
	}
	{
		unsigned long long d = ZSTD_findDecompressedSize(src, sr.n), b = ZSTD_decompressBound(src, sr.n);
		gp_assert(d == (allfcs ? sr.content_n : ZSTD_CONTENTSIZE_UNKNOWN) || (anybig && d == ZSTD_CONTENTSIZE_ERROR));
		gp_assert(b == bound || (anybig && b == ZSTD_CONTENTSIZE_ERROR));
	}
	free(src);
	free(dst);
	return 0;
}
