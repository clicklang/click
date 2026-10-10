/* Click's declaration-only <stdlib.h>: exactly the allocation functions
 * the kernel models. These declarations carry no executable semantics;
 * each call follows Click's allocation model, and a proof holds for any C
 * library that implements it.
 */
#pragma once
#ifndef NULL
#define NULL ((void*)0)
#endif
void *malloc(size_t size);
void *calloc(size_t count, size_t size);
void *realloc(void *pointer, size_t size);
void free(void *pointer);
