// Law api_flush_bound: For any input (any bytes, any length the allocator provides) given to ZSTD_decompressStream in
// any pieces with any output room, the stream reset after an error, every call given no input (input.pos ==
// input.size) writes at most ZSTD_BLOCKSIZE_MAX (128 KiB) bytes: zstd.h, ZSTD_decompressStream: "Note : with no
// additional input, amount of data flushed <= ZSTD_BLOCKSIZE_MAX."
#include "laws_common.h"

int main(void) {
	size_t n = upto(PTRDIFF_MAX), cap = upto(PTRDIFF_MAX);
	unsigned char *src = any_bytes(n), *dst = malloc(cap);
	ZSTD_DStream *zds = ZSTD_createDStream();
	if (src == NULL || dst == NULL || zds == NULL)
		return 0;
	ZSTD_inBuffer in;
	ZSTD_outBuffer out;
	in.src = src;
	in.size = 0;
	in.pos = 0;
	out.dst = dst;
	out.pos = 0;
	do {
		// Each call: the input so far and any more of it, any room after the output so far
		in.size += upto(n - in.size);
		out.size = out.pos + upto(cap - out.pos);
		size_t start = out.pos, no_input = in.pos == in.size;
		size_t result = ZSTD_decompressStream(zds, &out, &in);
		// Check
		if (no_input)
			gp_assert(out.pos - start <= ZSTD_BLOCKSIZE_MAX);
		if (ZSTD_isError(result))                    // zstd.h: after an error "it must be first reset"
			ZSTD_DCtx_reset(zds, ZSTD_reset_session_only);
	} while (nondet_u8() != 0);
	ZSTD_freeDStream(zds);
	return 0;
}
