/* SPDX-License-Identifier: GPL-2.0-or-later */
#ifndef RBTREE_SIZE_H
#define RBTREE_SIZE_H
#include "../rbtree-insert/rbtree.h"
struct sized_node { struct rb_node rb; int32 size; };

#define offsetof(TYPE, MEMBER) __builtin_offsetof(TYPE, MEMBER)
#define __same_type(a, b) __builtin_types_compatible_p(typeof(a), typeof(b))
#define static_assert _Static_assert
#define rb_entry(ptr, type, member) container_of(ptr, type, member)
#define container_of(ptr, type, member) ({				\
	void *__mptr = (void *)(ptr);					\
	static_assert(__same_type(*(ptr), ((type *)0)->member) ||	\
		      __same_type(*(ptr), void),			\
		      "pointer type mismatch in container_of()");	\
	((type *)(__mptr - offsetof(type, member))); })

#ifndef false
#define false 0
#endif
#ifndef true
#define true 1
#endif

#endif
