/* RingQ 1.2: a fixed-capacity queue of ints. */
#ifndef RINGQ_RINGQ_H
#define RINGQ_RINGQ_H

#include "rq_config.h"

struct RingQ {
	unsigned int head;
	unsigned int count;
	int slots[RQ_CAPACITY];
};

unsigned int RingQ_Capacity(void);
unsigned int RingQ_Next(unsigned int index);
int RingQ_IsFull(const struct RingQ *q);

#endif
