#include "state.h"

void FeeEnvelope::SetStamp(int next) noexcept { stamp = next; }
int FeeEnvelope::ReadStamp() const noexcept { return stamp; }
