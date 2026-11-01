// Law rj_any_stream: For any input (any bytes, any length the allocator provides) given to ZSTD_decompressStream in
// any pieces, each call with an input and an output buffer of any sizes and start positions (each an object of exactly
// its size), the stream reset (ZSTD_DCtx_reset) after an error, as zstd.h requires, and anywhere else or not, every
// call leaves input.pos and output.pos within their buffers and never moves them back: zstd.h, ZSTD_inBuffer and
// ZSTD_outBuffer, pos: "Will be updated. Necessarily 0 <= pos <= size".
#include "laws_common.h"

int main(void) {
	size_t n = upto(PTRDIFF_MAX), read = 0;
	unsigned char *input = any_bytes(n);
	ZSTD_DStream *zds = ZSTD_createDStream();
	if (input == NULL || zds == NULL)
		return 0;
	do {
		// Each call: the next piece of the input and any output space, objects of their own; any positions
		size_t take = upto(n - read), room = upto(PTRDIFF_MAX);
		unsigned char *piece = copy_of(input + read, take), *out = malloc(room);
		if ((piece == NULL && take != 0) || (out == NULL && room != 0))
			return 0;
		ZSTD_inBuffer in;
		ZSTD_outBuffer output;
		in.src = piece;
		in.size = take;
		in.pos = upto(take);
		output.dst = out;
		output.size = room;
		output.pos = upto(room);
		size_t in_start = in.pos, out_start = output.pos;
		size_t result = ZSTD_decompressStream(zds, &output, &in);
		// Check
		gp_assert(in_start <= in.pos && in.pos <= take && out_start <= output.pos && output.pos <= room);
		read += in.pos;
		free(piece);
		free(out);
		// zstd.h: after an error "it must be first reset"; at any other time, a reset or not
		if (ZSTD_isError(result) || nondet_u8() == 0)
			ZSTD_DCtx_reset(zds, ZSTD_reset_session_only);
	} while (nondet_u8() != 0);
	ZSTD_freeDStream(zds);
	return 0;
}
