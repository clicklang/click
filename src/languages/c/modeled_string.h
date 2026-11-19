/* Click's declaration-only <string.h>: exactly the functions that have a
 * standard-library contract. These declarations carry no executable
 * semantics; each call is checked against Click's specification of the
 * function, and a proof holds for any C library that implements it.
 */
/* Match glibc's guard so portable sources can skip their legacy fallback. */
#ifndef _STRING_H
#define _STRING_H 1
#ifndef NULL
#define NULL ((void*)0)
#endif
void *memcpy(void *dest, const void *src, size_t n);
int memcmp(const void *s1, const void *s2, size_t n);
void *memset(void *s, int c, size_t n);
size_t strlen(const char *s);
#endif /* _STRING_H */
