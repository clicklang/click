#include "state.h"

void FeeEnvelope::SetStamp(int next) noexcept { stamp = next; }
int FeeEnvelope::ReadStamp() const noexcept { return stamp; }

long long FeeEnvelope::ReadLeftFee() const noexcept { return (state.left).fee; }
void FeeEnvelope::SetRightFee(long long next) noexcept { this->state.right.fee = next; }
void FeeEnvelope::AddLeftSize(int delta) noexcept { state.left.size += delta; }
long long ReadRightFee(const PairState& pair) noexcept { return pair.right.fee; }
