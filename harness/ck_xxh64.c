// Law ck_xxh64: For any bytes (any length the allocator provides) and any seed, zstd's XXH64 (ZSTD_XXH64, the hash of
// the frame's Content_Checksum) equals XXH64 as the xxHash specification defines it, written out below.
#include "laws_common.h"

// xxHash specification (doc/xxhash_spec.md), "XXH64 Algorithm Description": "All operations are performed modulo 2^64".
#define PRIME64_1 0x9E3779B185EBCA87ULL
#define PRIME64_2 0xC2B2AE3D27D4EB4FULL
#define PRIME64_3 0x165667B19E3779F9ULL
#define PRIME64_4 0x85EBCA77C2B2AE63ULL
#define PRIME64_5 0x27D4EB2F165667C5ULL
static uint64_t rotl(uint64_t x, int r) { return x << r | x >> (64 - r); }   // "<<<", 0 < r < 64
static uint64_t le(const unsigned char *p, int size) {    // "read_64bit_little_endian", "read_32bit_little_endian"
	uint64_t value = 0;
	for (int i = size - 1; i >= 0; i--)
		value = value << 8 | p[i];
	return value;
}
static uint64_t round64(uint64_t acc, uint64_t lane) { return rotl(acc + lane * PRIME64_2, 31) * PRIME64_1; }
static uint64_t merge(uint64_t acc, uint64_t accn) { return (acc ^ round64(0, accn)) * PRIME64_1 + PRIME64_4; }

static uint64_t xxh64(const unsigned char *p, size_t len, uint64_t seed) {
	uint64_t acc = seed + PRIME64_5;                     // Step 1, "input is less than 32 bytes"
	size_t left = len;
	if (len >= 32) {                                      // Steps 1 to 3
		uint64_t acc1 = seed + PRIME64_1 + PRIME64_2, acc2 = seed + PRIME64_2;
		uint64_t acc3 = seed, acc4 = seed - PRIME64_1;
		for (; left >= 32; left -= 32, p += 32) {
			acc1 = round64(acc1, le(p, 8));
			acc2 = round64(acc2, le(p + 8, 8));
			acc3 = round64(acc3, le(p + 16, 8));
			acc4 = round64(acc4, le(p + 24, 8));
		}
		acc = rotl(acc1, 1) + rotl(acc2, 7) + rotl(acc3, 12) + rotl(acc4, 18);
		acc = merge(merge(merge(merge(acc, acc1), acc2), acc3), acc4);
	}
	acc += len;                                           // Step 4
	for (; left >= 8; left -= 8, p += 8)                  // Step 5
		acc = rotl(acc ^ round64(0, le(p, 8)), 27) * PRIME64_1 + PRIME64_4;
	if (left >= 4) {
		acc = rotl(acc ^ le(p, 4) * PRIME64_1, 23) * PRIME64_2 + PRIME64_3;
		left -= 4;
		p += 4;
	}
	for (; left >= 1; left--, p++)
		acc = rotl(acc ^ *p * PRIME64_5, 11) * PRIME64_1;
	acc = (acc ^ acc >> 33) * PRIME64_2;                  // Step 6
	acc = (acc ^ acc >> 29) * PRIME64_3;
	return acc ^ acc >> 32;
}

int main(void) {
	size_t len = upto(PTRDIFF_MAX);
	unsigned char *data = any_bytes(len);
	uint64_t seed;
	pick(seed);
	if (data == NULL)
		return 0;
	gp_assert(ZSTD_XXH64(data, len, seed) == xxh64(data, len, seed));
	return 0;
}
