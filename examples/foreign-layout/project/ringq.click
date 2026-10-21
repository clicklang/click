arithmetic "integer";

verifying "../upstream/RingQ-1.2/Source/RingQ_Core.c";

uint32 RingQ_Capacity() {
    ensures result == 8u32;
} by auto();

uint32 RingQ_Next(uint32 index) {
    ensures result < 8u32;
} by auto();

int32 RingQ_IsFull(const struct RingQ* q) {
    views q->count;
    ensures result == 1 or result == 0;
    ensures result == 1 implies q->count == 8u32;
} by auto();
