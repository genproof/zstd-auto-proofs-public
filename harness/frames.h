// frames.h: the simplest Zstandard frames, written field by field as RFC 8878 section 3.1 lays them out (Raw and RLE
// blocks, skippable frames), and streaming; shared by the laws on valid input. No model of the decoder.
#include "laws_common.h"
// The largest windows zstd decodes: in one call (zstd.h: ZSTD_WINDOWLOG_MAX, 31 on 64-bit), and streaming by default
// (zstd.h: "By default, a decompression context accepts window sizes <= (1 << ZSTD_WINDOWLOG_LIMIT_DEFAULT)", 2^27).
#define ONE_CALL_WINDOW ((uint64_t) 1 << ZSTD_WINDOWLOG_MAX)
#define STREAM_WINDOW ((uint64_t) 1 << ZSTD_WINDOWLOG_LIMIT_DEFAULT)
static void put_le(unsigned char *p, uint64_t value, size_t size) {   // RFC 8878: every field is little-endian
	for (size_t i = 0; i < size; i++)
		p[i] = (unsigned char) (value >> (8 * i));
}
// A Zstandard frame (3.1.1) for data[0..n-1] in a new object of *len bytes (NULL: out of memory): Magic_Number; a
// Frame_Header_Descriptor with any flags (the Unused_bit too: "a decoder ... shall not interpret this bit"; the
// Reserved_bit 0); a Window_Descriptor of any Window_Size up to max_window, or Single_Segment (then Window_Size = fcs,
// at most max_window); Frame_Content_Size fcs in any field that holds it, or none (not with Single_Segment); a
// Dictionary_ID field of any size that holds dict_id (none: only for 0); the data cut into Raw and RLE blocks of any
// sizes up to Block_Maximum_Size = min(Window_Size, 128 KiB), maybe an empty last block (an RLE block first makes its
// bytes one byte repeated: data changes); a Content_Checksum (the low 4 bytes of XXH64(data)) if its flag is set.
static unsigned char *new_frame(unsigned char *data, size_t n, uint64_t fcs, uint64_t max_window, uint32_t dict_id,
                                size_t *len) {
	unsigned char *f = n <= (PTRDIFF_MAX - 26) / 4 ? malloc(26 + 4 * n) : NULL;  // header, n + 1 blocks, checksum
	unsigned fcs_flag = nondet_u8() & 3, did_flag = nondet_u8() & 3;  // Frame_Content_Size_flag, Dictionary_ID_flag
	unsigned single = (nondet_u8() & 1) && fcs <= max_window;           // Single_Segment_flag
	if ((fcs_flag == 0 && single && fcs > 255) || (fcs_flag == 1 && (fcs < 256 || fcs > 65791)) ||
	    (fcs_flag == 2 && fcs > 0xFFFFFFFF))
		fcs_flag = 3;                        // FCS_Field_Size: 0 (1 if Single_Segment), 2 (fcs - 256), 4, 8
	if ((did_flag == 0 && dict_id != 0) || (did_flag == 1 && dict_id > 255) || (did_flag == 2 && dict_id > 65535))
		did_flag = 3;                        // DID_Field_Size: 0, 1, 2, 4
	unsigned fcs_size = fcs_flag == 0 ? single : 2u << (fcs_flag - 1), did_size = did_flag == 3 ? 4 : did_flag;
	unsigned char wd = nondet_u8();                  // Window_Descriptor: Exponent (bits 7-3), Mantissa (bits 2-0)
	uint64_t base = (uint64_t) 1 << (10 + (wd >> 3)), window = single ? fcs : base + base / 8 * (wd & 7);
	gp_assume(window <= max_window);
	if (f == NULL)
		return NULL;
	put_le(f, 0xFD2FB528, 4);
	f[4] = (unsigned char) (fcs_flag << 6 | single << 5 | (nondet_u8() & 0x14) | did_flag);   // bits 4 and 2: any
	f[5] = wd;                                       // (no Window_Descriptor with Single_Segment: overwritten)
	size_t at = single ? 5 : 6, done = 0, max_block = window < 131072 ? (size_t) window : 131072;
	put_le(f + at, dict_id, did_size);
	put_le(f + at + did_size, fcs_flag == 1 ? fcs - 256 : fcs, fcs_size);
	at += did_size + fcs_size;
	for (int last = 0; !last;) {         // Block_Header: Last_Block, Block_Type (0 Raw, 1 RLE), Block_Size
		size_t left = n - done, most = left < max_block ? left : max_block;
		size_t size = left == 0 ? 0 : 1 + upto(most == 0 ? 0 : most - 1);
		unsigned rle = (nondet_u8() & 1) && max_block > 0;          // an RLE block's content is 1 byte
		last = done + size == n && (size == 0 || (nondet_u8() & 1));
		put_le(f + at, (uint64_t) last | rle << 1 | size << 3, 3);
		at += 3;
		for (size_t i = 0; i < size; i++)
			if (rle)
				data[done + i] = data[done];
			else
				f[at++] = data[done + i];
		if (rle)
			f[at++] = size == 0 ? nondet_u8() : data[done];
		done += size;
	}
	if (f[4] & 4) {
		put_le(f + at, ZSTD_XXH64(data, n, 0), 4);
		at += 4;
	}
	*len = at;
	unsigned char *frame = copy_of(f, at);
	free(f);
	return frame;
}
// A skippable frame (3.1.2) in a new object of *len bytes (NULL: out of memory): Magic_Number 0x184D2A5? (any of the
// 16), Frame_Size, User_Data (any bytes, any length up to 2^32 - 1).
static unsigned char *new_skippable(size_t *len) {
	size_t size = upto(0xFFFFFFFF);
	unsigned char *f = malloc(8 + size);
	if (f == NULL)
		return NULL;
	put_le(f, 0x184D2A50 + (nondet_u8() & 15), 4);
	put_le(f + 4, size, 4);
	if (size != 0)
		nondet_bytes(f + 8, size);
	*len = 8 + size;
	return f;
}
// A new object holding a[0..a_len-1] then b[0..b_len-1] (NULL: out of memory, or a or b is); frees a and b.
static unsigned char *join(unsigned char *a, size_t a_len, unsigned char *b, size_t b_len) {
	int ok = (a != NULL || a_len == 0) && (b != NULL || b_len == 0) && a_len <= PTRDIFF_MAX - b_len;
	unsigned char *ab = ok ? malloc(a_len + b_len) : NULL;
	for (size_t i = 0; ab != NULL && i < a_len + b_len; i++)
		ab[i] = i < a_len ? a[i] : b[i - a_len];
	free(a);
	free(b);
	return ab;
}
// src[0..len-1] given to ZSTD_decompressStream on zds in any pieces with any output room in dst[0..cap-1] (at least a
// byte of each while any is left), until a call returns an error, or 0 ("a frame is completely decoded and fully
// flushed") with all of src read, or anything else having read and written nothing (zstd waits for input or room that
// is not there). Returns that last result; *written: the bytes output; *completed: how many calls returned 0.
static size_t stream_all(ZSTD_DStream *zds, const unsigned char *src, size_t len, unsigned char *dst, size_t cap,
                         size_t *written, size_t *completed) {
	ZSTD_inBuffer in;
	ZSTD_outBuffer out;
	size_t result, read, wrote;
	in.src = src;
	in.pos = 0;
	out.dst = dst;
	out.pos = 0;
	*completed = 0;
	do {
		read = in.pos;
		wrote = out.pos;
		in.size = in.pos == len ? len : in.pos + 1 + upto(len - in.pos - 1);
		out.size = out.pos == cap ? cap : out.pos + 1 + upto(cap - out.pos - 1);
		result = ZSTD_decompressStream(zds, &out, &in);
		*completed += result == 0;
	} while (!ZSTD_isError(result) && (result == 0 ? in.pos < len : in.pos != read || out.pos != wrote));
	*written = out.pos;
	return result;
}
