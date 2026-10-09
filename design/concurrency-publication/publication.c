#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>

struct channel {
    atomic_int ready;
    int payload;
};

void *producer(void *argument) {
    struct channel *channel = argument;
    channel->payload = 42;
    atomic_store_explicit(&channel->ready, 1, memory_order_release);
    return NULL;
}

int consume(struct channel *channel) {
    while (atomic_load_explicit(&channel->ready, memory_order_acquire) == 0) {
    }
    return channel->payload;
}

int publish_once(struct channel *channel) {
    pthread_t thread;
    int value;

    atomic_init(&channel->ready, 0);
    if (pthread_create(&thread, NULL, producer, channel) != 0) return -1;
    value = consume(channel);
    (void)pthread_join(thread, NULL);
    return value;
}
