#include "counter.h"

int bump_then_double(int& counter) noexcept {
    counter_add(counter, 1);
    int limit = counter_limit();
    int doubled = counter_double(counter);
    return doubled + limit;
}
