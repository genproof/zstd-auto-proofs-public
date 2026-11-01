// Law detect (PROMISES.md: V10, V11): ANY series of compliant frames in which one Zstandard frame is made invalid in
// a way zstd must detect: its Content_Checksum changed (zstd validates checksums by default: ZSTD_d_forceIgnoreChecksum
// "Default is 0"), or its Reserved_bit set ("A decoder compliant with this specification version must ensure it is not
// set").
//
// Claim (QuickProof.Contract.harness_safe of this program): no execution has undefined behaviour, and every gp_assert
// holds: one-shot decoding (ZSTD_decompress, any capacity) returns an error; streaming decoding (any chunks) never
// reports that frame complete (no 0 return at or after its end) before an error.
#include <stdlib.h>
#include "quickproof.h"
#include "writer.h"
#include "zlimits.h"

#define CALLS_MAX 4096

static wseries_t sr;

int main(void)
{
	unsigned k, kind = choose(2), j;
	size_t cap, r, end;
	unsigned char *src, *dst;
	w_series(&sr, 0);
	k = choose(sr.nframes);
	gp_assume(!sr.f[k].skippable);
	if (kind == 0) {
		unsigned x = 1 + choose(0xFFFFFFFFU);
		gp_assume(sr.f[k].checksum);
		for (j = 0; j < 4; j++)
			sr.bytes[sr.f[k].start + sr.f[k].size - 4 + j] ^= (unsigned char) ((x >> (8 * j)) & 255);
	} else {
		sr.bytes[sr.f[k].start + 4] |= 8;       /* Reserved_bit: bit 3 of Frame_Header_Descriptor */
	}
	end = sr.f[k].start + sr.f[k].size;
	src = exact_copy(sr.bytes, sr.n);
	if (src == NULL)
		return 0;                       /* harness out of memory: end the run */
	if (choose(2)) {
		cap = choose_in(0, sr.content_n + 16);
		dst = malloc(cap > 0 ? cap : 1);
		if (dst != NULL) {
			r = ZSTD_decompress(dst, cap, src, sr.n);
			gp_assert(ZSTD_isError(r));
			free(dst);
		}
	} else {
		ZSTD_DStream *ds = ZSTD_createDStream();
		size_t ipos = 0, calls;
		for (calls = 0; ds != NULL && calls < CALLS_MAX; calls++) {
			size_t ilen = choose_in(0, sr.n - ipos), olen = choose_in(1, sr.content_n + 1);
			unsigned char *ib = exact_copy(src + ipos, ilen), *ob = malloc(olen);
			ZSTD_inBuffer in;
			ZSTD_outBuffer out;
			if (ib == NULL || ob == NULL) {
				free(ib);
				free(ob);
				break;
			}
			in.src = ib;
			in.size = ilen;
			in.pos = 0;
			out.dst = ob;
			out.size = olen;
			out.pos = 0;
			r = ZSTD_decompressStream(ds, &out, &in);
			ipos += in.pos;
			free(ib);
			free(ob);
			if (ZSTD_isError(r))
				break;
			if (r == 0)
				gp_assert(ipos < end);
		}
		ZSTD_freeDStream(ds);
	}
	free(src);
	return 0;
}
