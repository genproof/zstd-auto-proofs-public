// laws_common.h: trivial helpers shared by the zstd laws (each law includes it once). No models, no algorithms.
#define ZSTD_STATIC_LINKING_ONLY                     // zstd.h's experimental part (ZSTD_WINDOWLOG_MAX, ...)
#include <stdint.h>
#include <stdlib.h>
#include "quickproof.h"
#include "zstd.h"
#include "zstd_errors.h"
uint64_t ZSTD_XXH64(const void *input, size_t length, uint64_t seed);   // zstd's XXH64 (law ck_xxh64 checks it)
static size_t upto(size_t max) {                    // any value from 0 to max
	size_t value = nondet_size();
	return value < max ? value : max;
}
static unsigned char *any_bytes(size_t n) {         // a new object of n arbitrary bytes (NULL if malloc fails)
	unsigned char *bytes = malloc(n);
	if (bytes != NULL && n != 0)
		nondet_bytes(bytes, n);
	return bytes;
}
static unsigned char *copy_of(const unsigned char *source, size_t n) {   // a new object holding source[0..n-1]
	unsigned char *copy = malloc(n);
	for (size_t i = 0; copy != NULL && i < n; i++)
		copy[i] = source[i];
	return copy;
}
static int bytes_eq(const unsigned char *a, const unsigned char *b, size_t n) {   // a[0..n-1] == b[0..n-1]
	for (size_t i = 0; i < n; i++)
		if (a[i] != b[i])
			return 0;
	return 1;
}
static int out_of_memory(size_t result) {           // zstd could not allocate (this ends a run: no claim)
	return ZSTD_getErrorCode(result) == ZSTD_error_memory_allocation;
}
