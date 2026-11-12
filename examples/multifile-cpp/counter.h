#ifndef COUNTER_H
#define COUNTER_H

int counter_add(int& counter, int amount) noexcept;
int counter_double(int& counter) noexcept;

inline int counter_limit() noexcept {
    return 1000;
}

#endif
