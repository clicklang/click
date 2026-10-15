# 0 "incremental.c"
# 0 "<built-in>"
# 0 "<command-line>"
# 1 "incremental.c"

# 1 "adler32.c" 1







# 1 "zutil.h" 1
# 22 "zutil.h"
# 1 "zlib.h" 1
# 34 "zlib.h"
# 1 "zconf.h" 1
# 254 "zconf.h"
# 1 "<stddef.h>" 1 3 4

       
# 255 "zconf.h" 2
     typedef size_t z_size_t;
# 393 "zconf.h"
typedef unsigned char Byte;

typedef unsigned int uInt;
typedef unsigned long uLong;





   typedef Byte Bytef;

typedef char charf;
typedef int intf;
typedef uInt uIntf;
typedef uLong uLongf;


   typedef void const *voidpc;
   typedef void *voidpf;
   typedef void *voidp;







# 1 "<limits.h>" 1 3 4

       
# 421 "zconf.h" 2
# 431 "zconf.h"
   typedef unsigned z_crc_t;
# 446 "zconf.h"
# 1 "<sys/types.h>" 1 3 4


       

# 4 "<sys/types.h>" 3 4
typedef long ssize_t;
typedef long off_t;
# 447 "zconf.h" 2





# 1 "<stdarg.h>" 1 3 4



       
typedef __builtin_va_list va_list;
# 453 "zconf.h" 2
# 35 "zlib.h" 2
# 81 "zlib.h"

# 81 "zlib.h"
typedef voidpf (*alloc_func)(voidpf opaque, uInt items, uInt size);
typedef void (*free_func)(voidpf opaque, voidpf address);

struct internal_state;

typedef struct z_stream_s {
    Bytef *next_in;
    uInt avail_in;
    uLong total_in;

    Bytef *next_out;
    uInt avail_out;
    uLong total_out;

    char *msg;
    struct internal_state *state;

    alloc_func zalloc;
    free_func zfree;
    voidpf opaque;

    int data_type;

    uLong adler;
    uLong reserved;
} z_stream;

typedef z_stream *z_streamp;





typedef struct gz_header_s {
    int text;
    uLong time;
    int xflags;
    int os;
    Bytef *extra;
    uInt extra_len;
    uInt extra_max;
    Bytef *name;
    uInt name_max;
    Bytef *comment;
    uInt comm_max;
    int hcrc;
    int done;

} gz_header;

typedef gz_header *gz_headerp;
# 220 "zlib.h"
extern const char * zlibVersion(void);
# 250 "zlib.h"
extern int deflate(z_streamp strm, int flush);
# 363 "zlib.h"
extern int deflateEnd(z_streamp strm);
# 401 "zlib.h"
extern int inflate(z_streamp strm, int flush);
# 521 "zlib.h"
extern int inflateEnd(z_streamp strm);
# 611 "zlib.h"
extern int deflateSetDictionary(z_streamp strm,
                                         const Bytef *dictionary,
                                         uInt dictLength);
# 655 "zlib.h"
extern int deflateGetDictionary(z_streamp strm,
                                         Bytef *dictionary,
                                         uInt *dictLength);
# 677 "zlib.h"
extern int deflateCopy(z_streamp dest,
                                z_streamp source);
# 695 "zlib.h"
extern int deflateReset(z_streamp strm);
# 706 "zlib.h"
extern int deflateParams(z_streamp strm,
                                  int level,
                                  int strategy);
# 744 "zlib.h"
extern int deflateTune(z_streamp strm,
                                int good_length,
                                int max_lazy,
                                int nice_length,
                                int max_chain);
# 761 "zlib.h"
extern uLong deflateBound(z_streamp strm,
                                   uLong sourceLen);
# 776 "zlib.h"
extern int deflatePending(z_streamp strm,
                                   unsigned *pending,
                                   int *bits);
# 791 "zlib.h"
extern int deflatePrime(z_streamp strm,
                                 int bits,
                                 int value);
# 808 "zlib.h"
extern int deflateSetHeader(z_streamp strm,
                                     gz_headerp head);
# 888 "zlib.h"
extern int inflateSetDictionary(z_streamp strm,
                                         const Bytef *dictionary,
                                         uInt dictLength);
# 911 "zlib.h"
extern int inflateGetDictionary(z_streamp strm,
                                         Bytef *dictionary,
                                         uInt *dictLength);
# 926 "zlib.h"
extern int inflateSync(z_streamp strm);
# 945 "zlib.h"
extern int inflateCopy(z_streamp dest,
                                z_streamp source);
# 961 "zlib.h"
extern int inflateReset(z_streamp strm);
# 972 "zlib.h"
extern int inflateReset2(z_streamp strm,
                                  int windowBits);
# 986 "zlib.h"
extern int inflatePrime(z_streamp strm,
                                 int bits,
                                 int value);
# 1007 "zlib.h"
extern long inflateMark(z_streamp strm);
# 1035 "zlib.h"
extern int inflateGetHeader(z_streamp strm,
                                     gz_headerp head);
# 1097 "zlib.h"
typedef unsigned (*in_func)(void *,
                            unsigned char * *);
typedef int (*out_func)(void *, unsigned char *, unsigned);

extern int inflateBack(z_streamp strm,
                                in_func in, void *in_desc,
                                out_func out, void *out_desc);
# 1171 "zlib.h"
extern int inflateBackEnd(z_streamp strm);







extern uLong zlibCompileFlags(void);
# 1232 "zlib.h"
extern int compress(Bytef *dest, uLongf *destLen,
                             const Bytef *source, uLong sourceLen);
# 1247 "zlib.h"
extern int compress2(Bytef *dest, uLongf *destLen,
                              const Bytef *source, uLong sourceLen,
                              int level);
# 1263 "zlib.h"
extern uLong compressBound(uLong sourceLen);






extern int uncompress(Bytef *dest, uLongf *destLen,
                               const Bytef *source, uLong sourceLen);
# 1288 "zlib.h"
extern int uncompress2(Bytef *dest, uLongf *destLen,
                                const Bytef *source, uLong *sourceLen);
# 1305 "zlib.h"
typedef struct gzFile_s *gzFile;
# 1345 "zlib.h"
extern gzFile gzdopen(int fd, const char *mode);
# 1368 "zlib.h"
extern int gzbuffer(gzFile file, unsigned size);
# 1384 "zlib.h"
extern int gzsetparams(gzFile file, int level, int strategy);
# 1395 "zlib.h"
extern int gzread(gzFile file, voidp buf, unsigned len);
# 1425 "zlib.h"
extern z_size_t gzfread(voidp buf, z_size_t size, z_size_t nitems,
                                 gzFile file);
# 1451 "zlib.h"
extern int gzwrite(gzFile file, voidpc buf, unsigned len);





extern z_size_t gzfwrite(voidpc buf, z_size_t size,
                                  z_size_t nitems, gzFile file);
# 1471 "zlib.h"
extern int gzprintf(gzFile file, const char *format, ...);
# 1486 "zlib.h"
extern int gzputs(gzFile file, const char *s);







extern char * gzgets(gzFile file, char *buf, int len);
# 1508 "zlib.h"
extern int gzputc(gzFile file, int c);





extern int gzgetc(gzFile file);
# 1523 "zlib.h"
extern int gzungetc(int c, gzFile file);
# 1535 "zlib.h"
extern int gzflush(gzFile file, int flush);
# 1570 "zlib.h"
extern int gzrewind(gzFile file);
# 1598 "zlib.h"
extern int gzeof(gzFile file);
# 1613 "zlib.h"
extern int gzdirect(gzFile file);
# 1634 "zlib.h"
extern int gzclose(gzFile file);
# 1647 "zlib.h"
extern int gzclose_r(gzFile file);
extern int gzclose_w(gzFile file);
# 1659 "zlib.h"
extern const char * gzerror(gzFile file, int *errnum);
# 1675 "zlib.h"
extern void gzclearerr(gzFile file);
# 1692 "zlib.h"
extern uLong adler32(uLong adler, const Bytef *buf, uInt len);
# 1712 "zlib.h"
extern uLong adler32_z(uLong adler, const Bytef *buf,
                                z_size_t len);
# 1730 "zlib.h"
extern uLong crc32(uLong crc, const Bytef *buf, uInt len);
# 1748 "zlib.h"
extern uLong crc32_z(uLong crc, const Bytef *buf,
                              z_size_t len);
# 1771 "zlib.h"
extern uLong crc32_combine_op(uLong crc1, uLong crc2, uLong op);
# 1784 "zlib.h"
extern int deflateInit_(z_streamp strm, int level,
                                 const char *version, int stream_size);
extern int inflateInit_(z_streamp strm,
                                 const char *version, int stream_size);
extern int deflateInit2_(z_streamp strm, int level, int method,
                                  int windowBits, int memLevel,
                                  int strategy, const char *version,
                                  int stream_size);
extern int inflateInit2_(z_streamp strm, int windowBits,
                                  const char *version, int stream_size);
extern int inflateBackInit_(z_streamp strm, int windowBits,
                                     unsigned char *window,
                                     const char *version,
                                     int stream_size);
# 1837 "zlib.h"
struct gzFile_s {
    unsigned have;
    unsigned char *next;
    long pos;
};
extern int gzgetc_(gzFile file);
# 1896 "zlib.h"
   extern gzFile gzopen(const char *, const char *);
   extern long gzseek(gzFile, long, int);
   extern long gztell(gzFile);
   extern long gzoffset(gzFile);
   extern uLong adler32_combine(uLong, uLong, long);
   extern uLong crc32_combine(uLong, uLong, long);
   extern uLong crc32_combine_gen(long);
# 1914 "zlib.h"
extern const char * zError(int);
extern int inflateSyncPoint(z_streamp);
extern const z_crc_t * get_crc_table(void);
extern int inflateUndermine(z_streamp, int);
extern int inflateValidate(z_streamp, int);
extern unsigned long inflateCodesUsed(z_streamp);
extern int inflateResetKeep(z_streamp);
extern int deflateResetKeep(z_streamp);






extern int gzvprintf(gzFile file,
                                           const char *format,
                                           va_list va);
# 23 "zutil.h" 2





# 1 "<string.h>" 1 3 4





       




# 10 "<string.h>" 3 4
void *memcpy(void *dest, const void *src, size_t n);
int memcmp(const void *s1, const void *s2, size_t n);
void *memset(void *s, int c, size_t n);
size_t strlen(const char *s);
# 29 "zutil.h" 2
# 1 "<stdlib.h>" 1 3 4





       



void *malloc(size_t size);
void *calloc(size_t count, size_t size);
void *realloc(void *pointer, size_t size);
void free(void *pointer);
# 30 "zutil.h" 2
# 39 "zutil.h"

# 39 "zutil.h"
typedef unsigned char uch;
typedef uch uchf;
typedef unsigned short ush;
typedef ush ushf;
typedef unsigned long ulg;
# 56 "zutil.h"
extern char * const z_errmsg[10];
# 173 "zutil.h"
    extern uLong adler32_combine64(uLong, uLong, long);
    extern uLong crc32_combine64(uLong, uLong, long);
    extern uLong crc32_combine_gen64(long);
# 240 "zutil.h"
   voidpf zcalloc(voidpf opaque, unsigned items,
                                unsigned size);
   void zcfree(voidpf opaque, voidpf ptr);
# 9 "adler32.c" 2
# 61 "adler32.c"
uLong adler32_z(uLong adler, const Bytef *buf, z_size_t len) {
    unsigned long sum2;
    unsigned n;


    sum2 = (adler >> 16) & 0xffff;
    adler &= 0xffff;


    if (len == 1) {
        adler += buf[0];
        if (adler >= 65521U)
            adler -= 65521U;
        sum2 += adler;
        if (sum2 >= 65521U)
            sum2 -= 65521U;
        return adler | (sum2 << 16);
    }


    if (buf == 0)
        return 1L;


    if (len < 16) {
        while (len--) {
            adler += *buf++;
            sum2 += adler;
        }
        if (adler >= 65521U)
            adler -= 65521U;
        sum2 %= 65521U;
        return adler | (sum2 << 16);
    }


    while (len >= 5552) {
        len -= 5552;
        n = 5552 / 16;
        do {
            {adler += (buf)[0]; sum2 += adler;}; {adler += (buf)[0 +1]; sum2 += adler;};; {adler += (buf)[0 +2]; sum2 += adler;}; {adler += (buf)[0 +2 +1]; sum2 += adler;};;; {adler += (buf)[0 +4]; sum2 += adler;}; {adler += (buf)[0 +4 +1]; sum2 += adler;};; {adler += (buf)[0 +4 +2]; sum2 += adler;}; {adler += (buf)[0 +4 +2 +1]; sum2 += adler;};;;; {adler += (buf)[8]; sum2 += adler;}; {adler += (buf)[8 +1]; sum2 += adler;};; {adler += (buf)[8 +2]; sum2 += adler;}; {adler += (buf)[8 +2 +1]; sum2 += adler;};;; {adler += (buf)[8 +4]; sum2 += adler;}; {adler += (buf)[8 +4 +1]; sum2 += adler;};; {adler += (buf)[8 +4 +2]; sum2 += adler;}; {adler += (buf)[8 +4 +2 +1]; sum2 += adler;};;;;;
            buf += 16;
        } while (--n);
        adler %= 65521U;
        sum2 %= 65521U;
    }


    if (len) {
        while (len >= 16) {
            len -= 16;
            {adler += (buf)[0]; sum2 += adler;}; {adler += (buf)[0 +1]; sum2 += adler;};; {adler += (buf)[0 +2]; sum2 += adler;}; {adler += (buf)[0 +2 +1]; sum2 += adler;};;; {adler += (buf)[0 +4]; sum2 += adler;}; {adler += (buf)[0 +4 +1]; sum2 += adler;};; {adler += (buf)[0 +4 +2]; sum2 += adler;}; {adler += (buf)[0 +4 +2 +1]; sum2 += adler;};;;; {adler += (buf)[8]; sum2 += adler;}; {adler += (buf)[8 +1]; sum2 += adler;};; {adler += (buf)[8 +2]; sum2 += adler;}; {adler += (buf)[8 +2 +1]; sum2 += adler;};;; {adler += (buf)[8 +4]; sum2 += adler;}; {adler += (buf)[8 +4 +1]; sum2 += adler;};; {adler += (buf)[8 +4 +2]; sum2 += adler;}; {adler += (buf)[8 +4 +2 +1]; sum2 += adler;};;;;;
            buf += 16;
        }
        while (len--) {
            adler += *buf++;
            sum2 += adler;
        }
        adler %= 65521U;
        sum2 %= 65521U;
    }


    return adler | (sum2 << 16);
}


uLong adler32(uLong adler, const Bytef *buf, uInt len) {
    return adler32_z(adler, buf, len);
}


static uLong adler32_combine_(uLong adler1, uLong adler2, long len2) {
    unsigned long sum1;
    unsigned long sum2;
    unsigned rem;


    if (len2 < 0)
        return 0xffffffffUL;


    len2 %= 65521U;
    rem = (unsigned)len2;
    sum1 = adler1 & 0xffff;
    sum2 = rem * sum1;
    sum2 %= 65521U;
    sum1 += (adler2 & 0xffff) + 65521U - 1;
    sum2 += ((adler1 >> 16) & 0xffff) + ((adler2 >> 16) & 0xffff) + 65521U - rem;
    if (sum1 >= 65521U) sum1 -= 65521U;
    if (sum1 >= 65521U) sum1 -= 65521U;
    if (sum2 >= ((unsigned long)65521U << 1)) sum2 -= ((unsigned long)65521U << 1);
    if (sum2 >= 65521U) sum2 -= 65521U;
    return sum1 | (sum2 << 16);
}


uLong adler32_combine(uLong adler1, uLong adler2, long len2) {
    return adler32_combine_(adler1, adler2, len2);
}

uLong adler32_combine64(uLong adler1, uLong adler2, long len2) {
    return adler32_combine_(adler1, adler2, len2);
}
# 3 "incremental.c" 2

uLong click_zlib_incremental(uLong seed, const Bytef *buf, z_size_t len,
                             z_size_t split)
{
    uLong prefix = adler32_z(seed, buf, split);
    return adler32_z(prefix, buf + split, len - split);
}
