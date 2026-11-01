// Law api_dict_id: For a Zstandard frame built by hand with any Dictionary_ID (frames.h, new_frame: an empty frame in
// any header form with a window up to ONE_CALL_WINDOW, the ID in a field of any size that holds it, or no field for
// ID 0) or a skippable frame (frames.h, new_skippable), followed by any bytes, ZSTD_getDictID_fromFrame returns that
// Dictionary_ID, and 0 for the skippable frame.
#include "frames.h"

int main(void) {
	// Choose the inputs: any ID; a frame with it, or a skippable frame; any bytes after it
	uint32_t dict_id = nondet_u32();
	unsigned char none[1];
	size_t len, after = upto(PTRDIFF_MAX);
	int skippable = nondet_u8() & 1;
	unsigned char *frame = skippable ? new_skippable(&len) : new_frame(none, 0, 0, ONE_CALL_WINDOW, dict_id, &len);
	unsigned char *src = frame == NULL ? NULL : join(frame, len, any_bytes(after), after);
	if (src == NULL)
		return 0;
	// Run zstd. zstd.h, ZSTD_getDictID_fromFrame: "Provides the dictID required to decompressed the frame stored
	// within `src`. If @return == 0, the dictID could not be decoded. This could for one of the following reasons :
	// - The frame does not require a dictionary to be decoded (most common case). ... - This is not a Zstandard
	// frame." RFC 8878 3.1.1.1.3: Dictionary_ID "contains the ID of the dictionary required to properly decode the
	// frame"
	unsigned id = ZSTD_getDictID_fromFrame(src, len + after);
	// Check
	gp_assert(id == (skippable ? 0 : dict_id));
	return 0;
}
