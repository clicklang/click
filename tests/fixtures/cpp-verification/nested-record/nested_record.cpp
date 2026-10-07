#include "state.h"

void FeeEnvelope::SetStamp(int next) noexcept { stamp = next; }
int FeeEnvelope::ReadStamp() const noexcept { return stamp; }

long long FeeEnvelope::ReadLeftFee() const noexcept { return (state.left).fee; }
void FeeEnvelope::SetRightFee(long long next) noexcept { this->state.right.fee = next; }
void FeeEnvelope::AddLeftSize(int delta) noexcept { state.left.size += delta; }
long long ReadRightFee(const PairState& pair) noexcept { return pair.right.fee; }

long long FeeState::ReadFee() const noexcept { return fee; }
void FeeState::SetFee(long long next) noexcept { fee = next; }
long long ReadFeeRef(const FeeState& state) noexcept { return state.fee; }
void SetFeeRef(FeeState& state, long long next) noexcept { state.fee = next; }
void BumpSizeRef(int& value) noexcept { value = value + 1; }
int ReadSizeRef(const int& value) noexcept { return value; }
long long FeeEnvelope::ReadLeftByMethod() const noexcept { return (state.left).ReadFee(); }
void FeeEnvelope::SetRightByMethod(long long next) noexcept { this->state.right.SetFee(next); }
long long FeeEnvelope::ReadRightByReference() const noexcept { return ReadFeeRef(state.right); }
void FeeEnvelope::SetLeftByReference(long long next) noexcept { SetFeeRef(state.left, next); }
void FeeEnvelope::BumpLeftByReference() noexcept { BumpSizeRef(state.left.size); }
int FeeEnvelope::ReadRightSizeByReference() const noexcept { return ReadSizeRef(state.right.size); }
