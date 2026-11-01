// Law api_content_size: For a Zstandard frame built by hand that declares any content size (frames.h, new_frame: an
// empty frame in any header form with a window up to ONE_CALL_WINDOW, Frame_Content_Size any value) or a skippable
// frame (frames.h, new_skippable), followed by any bytes, ZSTD_getFrameContentSize returns the declared size if the
// header has a Frame_Content_Size field, ZSTD_CONTENTSIZE_UNKNOWN if it has none, and 0 for the skippable frame.
#include "frames.h"

int main(void) {
	// Choose the inputs: any declared size; a frame declaring it, or a skippable frame; any bytes after it
	uint64_t declared;
	pick(declared);
	unsigned char none[1];
	size_t len, after = upto(PTRDIFF_MAX);
	int skippable = nondet_u8() & 1;
	unsigned char *frame = skippable ? new_skippable(&len)
	                                 : new_frame(none, 0, declared, ONE_CALL_WINDOW, 0, &len);
	unsigned char *src = frame == NULL ? NULL : join(frame, len, any_bytes(after), after);
	if (src == NULL)
		return 0;
	// Run zstd. zstd.h, ZSTD_getFrameContentSize: "@return The decompressed size in bytes when the value is
	// available in the frame header"; "@retval ZSTD_CONTENTSIZE_UNKNOWN The frame does not encode a decompressed
	// size"; "Skippable frames also report 0". RFC 8878 3.1.1.1.1: "When Flag_Value is 0, FCS_Field_Size depends on
	// Single_Segment_flag"
	unsigned long long size = ZSTD_getFrameContentSize(src, len + after);
	// Check
	if (skippable)
		gp_assert(size == 0);
	else if ((src[4] >> 6) == 0 && !(src[4] & 0x20))
		gp_assert(size == ZSTD_CONTENTSIZE_UNKNOWN);
	else
		gp_assert(size == declared);
	return 0;
}
