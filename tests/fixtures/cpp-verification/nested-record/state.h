#pragma once

struct FeeState {
    long long fee;
    int size;
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
};
