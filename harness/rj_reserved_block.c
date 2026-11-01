// Law rj_reserved_block: A Zstandard frame built by hand (frames.h, new_frame: any data of any length the allocator
// provides, any header form with a window up to STREAM_WINDOW, any blocks, a checksum or not) with the Block_Type of
// any one of its blocks changed to 3 (Reserved) is refused: ZSTD_decompress, with any capacity, returns an error, and
// ZSTD_decompressStream, given it in any pieces with any output room (frames.h, stream_all), never reports the frame
// complete (ZSTD_error_memory_allocation ends the run).
#include "frames.h"

int main(void) {
	// Choose the inputs: any data, any frame for it, any one of its blocks, any capacity
	size_t n = upto(PTRDIFF_MAX), len, written, completed;
	unsigned char *data = any_bytes(n);
	unsigned char *frame = data == NULL ? NULL : new_frame(data, n, n, STREAM_WINDOW, 0, &len);
	size_t cap = upto(PTRDIFF_MAX);
	unsigned char *dst = malloc(cap);
	ZSTD_DStream *zds = ZSTD_createDStream();
	if (frame == NULL || dst == NULL || zds == NULL)
		return 0;
	// RFC 8878 3.1.1.1: the first Block_Header follows Magic_Number (4 bytes), Frame_Header_Descriptor (1),
	// Window_Descriptor (1, none with Single_Segment_flag), Dictionary_ID (0, 1, 2, 4), Frame_Content_Size (0 or 1
	// with Single_Segment_flag, 2, 4, 8); a block is its 3-byte header and Block_Size bytes (Raw) or 1 byte (RLE)
	unsigned fhd = frame[4], single = fhd >> 5 & 1, fcs_flag = fhd >> 6;
	size_t at = 5 + !single + (fhd & 3) + ((fhd & 3) == 3) + (fcs_flag == 0 ? single : 1u << fcs_flag);
	for (unsigned skip = nondet_u8(); skip > 0 && !(frame[at] & 1); skip--)   // any block, not past the last one
		at += 3 + ((frame[at] >> 1 & 3) == 1 ? 1 : (frame[at] | frame[at + 1] << 8 | frame[at + 2] << 16) >> 3);
	frame[at] |= 6;                                  // Block_Type (bits 1-2): 3
	// Run zstd. RFC 8878 3.1.1.2.2: "Reserved - this is not a block. This value cannot be used with current version
	// of this specification. If such a value is present, it is considered corrupted data."
	size_t result = ZSTD_decompress(dst, cap, frame, len);
	size_t last = stream_all(zds, frame, len, dst, cap, &written, &completed);
	if (out_of_memory(result) || out_of_memory(last))
		return 0;
	// Check
	gp_assert(ZSTD_isError(result) && completed == 0);
	return 0;
}
