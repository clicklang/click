#include "state.h"

bool FeeRateState::IsEmpty() const noexcept { return size == 0; }
long long FeeRateState::ReadFee() const noexcept { return fee; }
void FeeRateState::SetFee(long long next) noexcept { fee = next; }
