# 0 "label_copy.c"
# 0 "<built-in>"
# 0 "<command-line>"
# 1 "label_copy.c"
# 1 "<string.h>" 1 3 4





       




# 10 "<string.h>" 3 4
void *memcpy(void *dest, const void *src, size_t n);
int memcmp(const void *s1, const void *s2, size_t n);
void *memset(void *s, int c, size_t n);
size_t strlen(const char *s);
# 2 "label_copy.c" 2
# 1 "label.h" 1




# 4 "label.h"
unsigned long label_fit(unsigned long length);
unsigned long label_measure(const char *src);
unsigned long label_copy(char *dst, const char *src);
# 3 "label_copy.c" 2


unsigned long label_measure(const char *src)
{
 return label_fit(strlen(src));
}


unsigned long label_copy(char *dst, const char *src)
{
 unsigned long n = label_fit(strlen(src));

 memcpy(dst, src, n);
 dst[n] = '\0';
 return n;
}
