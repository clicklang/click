#include "counter.h"

int counter_add(int& counter, int amount) noexcept {
    counter = counter + amount;
    return counter;
}

int counter_double(int& counter) noexcept {
    counter = counter + counter;
    return counter;
}
