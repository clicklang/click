#pragma once

class FeeRateState {
    long long fee;
    int size;
public:
    bool IsEmpty() const noexcept;
    long long ReadFee() const noexcept;
    void SetFee(long long next) noexcept;
};

// A declaration outside the selected graph must not become a proof obligation.
class Unrelated { virtual void operation() = 0; };
