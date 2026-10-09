#include <pthread.h>
#include <stddef.h>

struct vector {
    int32 len;
    int32 cap;
    int32* data;
};

struct shared_log {
    pthread_mutex_t mu;
    struct vector* items;
};

void *producer(void *argument) {
    struct shared_log *log = argument;
    (void)pthread_mutex_lock(&log->mu);
    (void)allocated_vector_push(log->items, 7);
    (void)pthread_mutex_unlock(&log->mu);
    return NULL;
}

int32 run_two_producers(struct shared_log *log) {
    pthread_t first;
    pthread_t second;

    if (pthread_mutex_init(&log->mu, NULL) != 0) return 0;
    if (pthread_create(&first, NULL, producer, log) != 0) {
        (void)pthread_mutex_destroy(&log->mu);
        return 0;
    }
    if (pthread_create(&second, NULL, producer, log) != 0) {
        (void)pthread_join(first, NULL);
        (void)pthread_mutex_destroy(&log->mu);
        return 0;
    }
    (void)pthread_join(first, NULL);
    (void)pthread_join(second, NULL);
    (void)pthread_mutex_destroy(&log->mu);
    return 1;
}
