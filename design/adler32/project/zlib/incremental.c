/* Two actual updates through the unchanged pinned zlib implementation. */
#include "adler32.c"

uLong click_zlib_incremental(uLong seed, const Bytef *buf, z_size_t len,
                             z_size_t split)
{
    uLong prefix = adler32_z(seed, buf, split);
    return adler32_z(prefix, buf + split, len - split);
}
