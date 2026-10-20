# A discarded `do_div` runs its statement expression

Linux's `do_div(n, base)` from `include/asm-generic/div64.h` is a GNU
statement expression: it divides `n` in place and yields the remainder.
`string_get_size` calls it as a statement, `do_div(blk_size,
divisor[units_base]);`, and discards the remainder. An expression statement
evaluates its expression for its effects and discards the value (C11
6.8.3p2): the division and the assignment to `n` happen, and the remainder is
still computed, so an operation that is undefined there is still checked.
The macro and the call are unchanged.

```c filename=do_div.c
typedef unsigned int uint32_t;
typedef unsigned long uint64_t;

/* include/asm-generic/div64.h, BITS_PER_LONG == 64 */
# define do_div(n,base) ({					\
	uint32_t __base = (base);				\
	uint32_t __rem;						\
	__rem = ((uint64_t)(n)) % __base;			\
	(n) = ((uint64_t)(n)) / __base;				\
	__rem;							\
 })

unsigned long reduce(unsigned long blk_size, unsigned int divisor)
{
	do_div(blk_size, divisor);
	return blk_size;
}

int discard_cast(int x)
{
	(void)(x = x + 1);
	return x;
}
```

```click
verifying "do_div.c";

uint64 reduce(uint64 blk_size, uint32 divisor) {
    requires blk_size == 2005 and divisor == 1000;
    ensures result == 2;
} by {
    execute();
    simp();
}

int32 discard_cast(int32 x) {
    requires x == 4;
    ensures result == 5;
} by {
    execute();
    simp();
}
```

```expect
pass
```
