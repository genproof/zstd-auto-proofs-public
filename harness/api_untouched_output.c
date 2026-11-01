// Law api_untouched_output: For any input (any bytes, any length the allocator provides) given to
// ZSTD_decompressStream in any pieces, each call with any output space and start position (each piece and each output
// space an object of exactly its size), the stream reset after an error, no call changes the output space before the
// position it is given, and every call that returns no error writes only up to the position it returns: the bytes
// after it are as they were (an error leaves pos where it was, and the stream "in undefined state", zstd.h).
#include "laws_common.h"

int main(void) {
	size_t n = upto(PTRDIFF_MAX), read = 0;
	unsigned char *input = any_bytes(n);
	ZSTD_DStream *zds = ZSTD_createDStream();
	if (input == NULL || zds == NULL)
		return 0;
	do {
		// Each call: the next piece of the input and any output space with any start, as objects of their own
		size_t take = upto(n - read), room = upto(PTRDIFF_MAX);
		unsigned char *piece = copy_of(input + read, take), *out = any_bytes(room);
		unsigned char *before = out == NULL ? NULL : copy_of(out, room);
		if ((piece == NULL && take != 0) || (before == NULL && room != 0))
			return 0;
		ZSTD_inBuffer in;
		ZSTD_outBuffer output;
		in.src = piece;
		in.size = take;
		in.pos = 0;
		output.dst = out;
		output.size = room;
		output.pos = upto(room);
		size_t start = output.pos;
		size_t result = ZSTD_decompressStream(zds, &output, &in);
		// Check. zstd.h, ZSTD_outBuffer: pos is the "position where writing stopped"
		if (room != 0)
			gp_assert(bytes_eq(out, before, start) &&
			          (ZSTD_isError(result) || bytes_eq(out + output.pos, before + output.pos, room - output.pos)));
		read += in.pos;
		free(piece);
		free(out);
		free(before);
		if (ZSTD_isError(result))                    // zstd.h: after an error "it must be first reset"
			ZSTD_DCtx_reset(zds, ZSTD_reset_session_only);
	} while (nondet_u8() != 0);
	ZSTD_freeDStream(zds);
	return 0;
}
