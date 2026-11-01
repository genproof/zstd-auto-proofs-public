// The decoder as one translation unit (as upstream's build/single_file_libs/zstddeclib-in.c): genproof's
// interpreter runs merge units and rename each .c file's own names, which breaks zstd's struct tags
// declared in shared headers (zstd.h: typedef struct ZSTD_DDict_s ZSTD_DDict).  One unit for clight.sh too.
#include "../lib/common/debug.c"
#include "../lib/common/entropy_common.c"
#include "../lib/common/error_private.c"
#include "../lib/common/fse_decompress.c"
#include "../lib/common/xxhash.c"
#include "../lib/common/zstd_common.c"
#include "../lib/decompress/huf_decompress.c"
#include "../lib/decompress/zstd_ddict.c"
#include "../lib/decompress/zstd_decompress.c"
#include "../lib/decompress/zstd_decompress_block.c"
