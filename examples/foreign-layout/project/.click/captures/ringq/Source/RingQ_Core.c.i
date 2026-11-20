# 0 "Source/RingQ_Core.c"
# 0 "<built-in>"
# 0 "<command-line>"
# 1 "Source/RingQ_Core.c"
# 1 "inc/ringq/RingQ.h" 1




# 1 "../../project/build/gen/rq_config.h" 1
# 6 "inc/ringq/RingQ.h" 2

struct RingQ {
 unsigned int head;
 unsigned int count;
 int slots[8u];
};

unsigned int RingQ_Capacity(void);
unsigned int RingQ_Next(unsigned int index);
int RingQ_IsFull(const struct RingQ *q);
# 2 "Source/RingQ_Core.c" 2

unsigned int RingQ_Capacity(void)
{
 return 8u;
}


unsigned int RingQ_Next(unsigned int index)
{
 return (index + 1u) % 8u;
}

int RingQ_IsFull(const struct RingQ *q)
{
 return q->count == 8u;
}
