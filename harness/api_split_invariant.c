// Law api_split_invariant: For any ZSTD_d_windowLogMax that zstd accepts, any series of Zstandard and skippable frames
// built by hand (as in rfc_skippable, with windows up to 2^windowLogMax bytes, STREAM_WINDOW for the default 0) and any
// output capacity, ZSTD_decompressStream given the series in any pieces with any output room (frames.h, stream_all)
// ends as ZSTD_decompress of the whole series does: when that fails, the stream never ends with 0 after reading all of
// it; when it succeeds, the stream does, with exactly the same bytes (ZSTD_error_memory_allocation ends the run).
#include "frames.h"

int main(void) {
	// Choose the inputs: any accepted windowLogMax; any series (Zstandard and skippable frames); any capacity
	int window_log = (int) nondet_u32();
	ZSTD_DStream *zds = ZSTD_createDStream();
	if (zds == NULL || ZSTD_isError(ZSTD_DCtx_setParameter(zds, ZSTD_d_windowLogMax, window_log)))
		return 0;
	uint64_t max_window = window_log == 0 ? STREAM_WINDOW : (uint64_t) 1 << window_log;
	size_t n = upto(PTRDIFF_MAX), done = 0, series_len = 0, len, written, completed;
	unsigned char *data = any_bytes(n), *series = NULL;
	if (data == NULL)
		return 0;
	do {
		size_t piece = 0;
		unsigned char *frame;
		if (nondet_u8() & 1) {
			frame = new_skippable(&len);
		} else {
			piece = upto(n - done);
			frame = new_frame(data + done, piece, piece, max_window, 0, &len);
		}
		series = frame == NULL ? NULL : join(series, series_len, frame, len);
		if (series == NULL)
			return 0;
		series_len += len;
		done += piece;
	} while (done < n || nondet_u8() != 0);
	size_t cap = upto(PTRDIFF_MAX);
	unsigned char *one = malloc(cap), *streamed = malloc(cap);
	if (one == NULL || streamed == NULL)
		return 0;
	// Run zstd: one call, and the stream
	size_t result = ZSTD_decompress(one, cap, series, series_len);
	size_t last = stream_all(zds, series, series_len, streamed, cap, &written, &completed);
	if (out_of_memory(result) || out_of_memory(last))
		return 0;
	// Check. zstd.h, ZSTD_decompressStream: "@return : 0 when a frame is completely decoded and fully flushed"
	if (ZSTD_isError(result))
		gp_assert(last != 0);
	else
		gp_assert(last == 0 && written == result && bytes_eq(streamed, one, result));
	return 0;
}
