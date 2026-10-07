#pragma once

struct FeeState {
    long long fee;
    int size;
    long long ReadFee() const noexcept;
    void SetFee(long long next) noexcept;
};

struct PairState {
    FeeState left;
    FeeState right;
    int generation;
};

class FeeEnvelope {
    PairState state;
    int stamp;
public:
    void SetStamp(int next) noexcept;
    int ReadStamp() const noexcept;
    long long ReadLeftFee() const noexcept;
    void SetRightFee(long long next) noexcept;
    void AddLeftSize(int delta) noexcept;
    long long ReadLeftByMethod() const noexcept;
    void SetRightByMethod(long long next) noexcept;
    long long ReadRightByReference() const noexcept;
    void SetLeftByReference(long long next) noexcept;
    void BumpLeftByReference() noexcept;
    int ReadRightSizeByReference() const noexcept;
};
