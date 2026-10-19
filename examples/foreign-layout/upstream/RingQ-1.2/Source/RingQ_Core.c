#include "ringq/RingQ.h"

unsigned int RingQ_Capacity(void)
{
	return RQ_CAPACITY;
}

/* The slot after `index`, wrapping at the capacity. */
unsigned int RingQ_Next(unsigned int index)
{
	return (index + 1u) % RQ_CAPACITY;
}

int RingQ_IsFull(const struct RingQ *q)
{
	return q->count == RQ_CAPACITY;
}
