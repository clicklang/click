# Conditional loop ownership must hold at entry

```c filename=mutex_held_parity.c
#include <pthread.h>
#include <stddef.h>

struct parity_mutex {
    pthread_mutex_t mutex;
};

int alternate_mutex(struct parity_mutex *object, int n) {
    if (pthread_mutex_init(&object->mutex, NULL) != 0) return 0;

    int i = 0;
    while (i < n) {
        if (i % 2 == 0) {
            (void)pthread_mutex_lock(&object->mutex);
        } else {
            (void)pthread_mutex_unlock(&object->mutex);
        }
        i++;
    }

    if (i % 2 != 0) (void)pthread_mutex_unlock(&object->mutex);
    (void)pthread_mutex_destroy(&object->mutex);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_held_parity.c";

theorem bounded_one(r: int32) {
    requires 1 <= r;
    requires r <= 1;
    ensures r == 1 by { arithmetic() using { 1 <= r; r <= 1; } }
}

theorem nonzero_nonnegative(r: int32) {
    requires 0 <= r;
    requires r != 0;
    ensures 1 <= r by { arithmetic() using { 0 <= r; r != 0; } }
}
theorem even_successor(i: int32) {
    requires 0 <= i;
    requires i < 2147483647;
    requires i % 2 == 0;
    ensures (i + 1) % 2 == 1 by {
        have 0 <= i % 2 by { arithmetic() using { i % 2 == 0; } }
        have i % 2 <= 0 by { arithmetic() using { i % 2 == 0; } }
        arithmetic() using { 0 <= i; i < 2147483647; 0 <= i % 2; i % 2 <= 0; }
    }
}
theorem odd_successor(i: int32) {
    requires 0 <= i;
    requires i < 2147483647;
    requires i % 2 != 0;
    ensures (i + 1) % 2 == 0 by {
        have 0 <= i % 2 by { arithmetic() using { 0 <= i; } }
        have i % 2 < 2 by { arithmetic() using { 0 <= i; } }
        have 1 <= i % 2 by { apply(nonzero_nonnegative(i % 2)); }
        have i % 2 <= 1 by { arithmetic() using { 0 <= i; i % 2 < 2; } }
        arithmetic() using { 0 <= i; i < 2147483647; 1 <= i % 2; i % 2 <= 1; }
    }
}

int32 alternate_mutex(struct parity_mutex *object, int32 n) {
    owns object->mutex;
    requires aligned(&object->mutex, 8);
    ensures result == 1;
} by {
    step();
    step();
    step();
    step();
    step();
    if n < 0 {
        loop {
            decreases n - i;
            invariant i == 0;
            invariant n < 0;
        }
        execute();
        simp();
    } else {
        have n >= 0 by simp;
        loop {
            if i % 2 == 0 {
                owns mutex_guard(&object->mutex);
            }
            owns mutex_live(&object->mutex);
            owns object->mutex;
            decreases n - i;
            invariant 0 <= i and i <= n;
            initialize by simp;
            preserve by {
                have i < 2147483647 by { arithmetic() using { i < n; } }
                if i % 2 == 0 {
                    have (i + 1) % 2 == 1 by { apply(even_successor(i)); }
                    step();
                    step();
                    step();
                    close_invariants();
                } else {
                    have (i + 1) % 2 == 0 by { apply(odd_successor(i)); }
                    have 0 <= i % 2 by { arithmetic() using { 0 <= i; } }
                    have 1 <= i % 2 by { apply(nonzero_nonnegative(i % 2)); }
                    have i % 2 <= 1 by { arithmetic() using { 0 <= i; } }
                    have i % 2 == 1 by { apply(bounded_one(i % 2)); }
                    step();
                    step();
                    step();
                    close_invariants();
                }
            }
        }
        if i % 2 == 0 {
            execute();
            simp();
        } else {
            have 0 <= i % 2 by { arithmetic() using { 0 <= i; } }
            have 1 <= i % 2 by { apply(nonzero_nonnegative(i % 2)); }
            have i % 2 <= 1 by { arithmetic() using { 0 <= i; } }
            have i % 2 == 1 by { apply(bounded_one(i % 2)); }
            execute();
            simp();
        }
    }
}
```

```expect
fail: mutex_guard
```
