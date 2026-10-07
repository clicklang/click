/* Two users share one reference-counted object with its owner. The owner
 * retains a reference for each user under the object's mutex, hands it to
 * the user's thread, and each user releases it under the same mutex. After
 * both users finish, the owner releases its own reference and reclaims the
 * object. */
#include <pthread.h>
#include <stddef.h>

struct object {
    pthread_mutex_t mu;
    int refs;
};

void object_retain(struct object *obj) {
    pthread_mutex_lock(&obj->mu);
    obj->refs = obj->refs + 1;
    pthread_mutex_unlock(&obj->mu);
}

void object_release(struct object *obj) {
    pthread_mutex_lock(&obj->mu);
    obj->refs = obj->refs - 1;
    pthread_mutex_unlock(&obj->mu);
}

void *user(void *argument) {
    struct object *obj = argument;
    object_release(obj);
    return NULL;
}

int run(void) {
    pthread_t a;
    pthread_t b;
    struct object *obj = malloc(sizeof(struct object));
    if (obj == 0) return -1;
    obj->refs = 1;
    pthread_mutex_init(&obj->mu, 0);
    object_retain(obj);
    if (pthread_create(&a, NULL, user, obj) != 0) {
        object_release(obj);
        object_release(obj);
        pthread_mutex_destroy(&obj->mu);
        free(obj);
        return 0;
    }
    object_retain(obj);
    if (pthread_create(&b, NULL, user, obj) != 0) {
        object_release(obj);
        pthread_join(a, NULL);
        object_release(obj);
        pthread_mutex_destroy(&obj->mu);
        free(obj);
        return 0;
    }
    pthread_join(a, NULL);
    pthread_join(b, NULL);
    object_release(obj);
    pthread_mutex_destroy(&obj->mu);
    free(obj);
    return 1;
}

int run_reverse_join(void) {
    pthread_t a;
    pthread_t b;
    struct object *obj = malloc(sizeof(struct object));
    if (obj == 0) return -1;
    obj->refs = 1;
    pthread_mutex_init(&obj->mu, 0);
    object_retain(obj);
    if (pthread_create(&a, NULL, user, obj) != 0) {
        object_release(obj);
        object_release(obj);
        pthread_mutex_destroy(&obj->mu);
        free(obj);
        return 0;
    }
    object_retain(obj);
    if (pthread_create(&b, NULL, user, obj) != 0) {
        object_release(obj);
        pthread_join(a, NULL);
        object_release(obj);
        pthread_mutex_destroy(&obj->mu);
        free(obj);
        return 0;
    }
    pthread_join(b, NULL);
    pthread_join(a, NULL);
    object_release(obj);
    pthread_mutex_destroy(&obj->mu);
    free(obj);
    return 1;
}
