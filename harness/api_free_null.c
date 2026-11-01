// Law api_free_null: ZSTD_freeDCtx, ZSTD_freeDStream and ZSTD_freeDDict accept a null pointer: each returns a result
// that is not an error (zstd.h: ZSTD_freeDCtx, ZSTD_freeDStream "accept NULL pointer"; ZSTD_freeDDict "If a NULL
// pointer is passed, no operation is performed").
#include "laws_common.h"

int main(void) {
	gp_assert(!ZSTD_isError(ZSTD_freeDCtx(NULL)) && !ZSTD_isError(ZSTD_freeDStream(NULL)) &&
	          !ZSTD_isError(ZSTD_freeDDict(NULL)));
	return 0;
}
