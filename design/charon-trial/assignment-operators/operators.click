verifying "operators.rs";

void U32X4_mul_assign_u32(struct U32X4* self, uint32 rhs) {
    requires rhs == 2u32;
    requires self->_0[0] <= 1000u32;
    requires self->_0[1] <= 1000u32;
    requires self->_0[2] <= 1000u32;
    requires self->_0[3] <= 1000u32;
    owns self->_0[0..4];
    ensures self->_0[0] == old(self->_0[0]) * rhs;
    ensures self->_0[1] == old(self->_0[1]) * rhs;
    ensures self->_0[2] == old(self->_0[2]) * rhs;
    ensures self->_0[3] == old(self->_0[3]) * rhs;
} by { execute(); simp(); }

void scaled(struct U32X4* words, uint32 factor) {
    requires factor == 2u32;
    requires words->_0[0] <= 1000u32;
    requires words->_0[1] <= 1000u32;
    requires words->_0[2] <= 1000u32;
    requires words->_0[3] <= 1000u32;
    owns words->_0[0..4];
    ensures words->_0[0] == old(words->_0[0]) * factor;
    ensures words->_0[1] == old(words->_0[1]) * factor;
    ensures words->_0[2] == old(words->_0[2]) * factor;
    ensures words->_0[3] == old(words->_0[3]) * factor;
} by { execute(); simp(); }

void U32X4_rem_assign_u32(struct U32X4* self, uint32 quotient) {
    requires quotient != 0u32;
    owns self->_0[0..4];
    ensures self->_0[0] == old(self->_0[0]) % quotient;
    ensures self->_0[1] == old(self->_0[1]) % quotient;
    ensures self->_0[2] == old(self->_0[2]) % quotient;
    ensures self->_0[3] == old(self->_0[3]) % quotient;
} by { execute(); simp(); }

void reduced(struct U32X4* words, uint32 divisor) {
    requires divisor != 0u32;
    owns words->_0[0..4];
    ensures words->_0[0] == old(words->_0[0]) % divisor;
    ensures words->_0[1] == old(words->_0[1]) % divisor;
    ensures words->_0[2] == old(words->_0[2]) % divisor;
    ensures words->_0[3] == old(words->_0[3]) % divisor;
} by { execute(); simp(); }

void U32X4_add_assign_ref_U32X4(struct U32X4* self, const struct U32X4* other) {
    requires separate(memory(self->_0[0..4]), memory(other->_0[0..4]));
    views other->_0[0..4];
    requires self->_0[0] <= 1000u32;
    requires other->_0[0] <= 1000u32;
    requires self->_0[1] <= 1000u32;
    requires other->_0[1] <= 1000u32;
    requires self->_0[2] <= 1000u32;
    requires other->_0[2] <= 1000u32;
    requires self->_0[3] <= 1000u32;
    requires other->_0[3] <= 1000u32;
    owns self->_0[0..4];
    ensures self->_0[0] == old(self->_0[0]) + old(other->_0[0]);
    ensures other->_0[0] == old(other->_0[0]);
    ensures self->_0[1] == old(self->_0[1]) + old(other->_0[1]);
    ensures other->_0[1] == old(other->_0[1]);
    ensures self->_0[2] == old(self->_0[2]) + old(other->_0[2]);
    ensures other->_0[2] == old(other->_0[2]);
    ensures self->_0[3] == old(self->_0[3]) + old(other->_0[3]);
    ensures other->_0[3] == old(other->_0[3]);
} by { execute(); simp(); }

void added(struct U32X4* words, const struct U32X4* other) {
    requires separate(memory(words->_0[0..4]), memory(other->_0[0..4]));
    views other->_0[0..4];
    requires words->_0[0] <= 1000u32;
    requires other->_0[0] <= 1000u32;
    requires words->_0[1] <= 1000u32;
    requires other->_0[1] <= 1000u32;
    requires words->_0[2] <= 1000u32;
    requires other->_0[2] <= 1000u32;
    requires words->_0[3] <= 1000u32;
    requires other->_0[3] <= 1000u32;
    owns words->_0[0..4];
    ensures words->_0[0] == old(words->_0[0]) + old(other->_0[0]);
    ensures other->_0[0] == old(other->_0[0]);
    ensures words->_0[1] == old(words->_0[1]) + old(other->_0[1]);
    ensures other->_0[1] == old(other->_0[1]);
    ensures words->_0[2] == old(words->_0[2]) + old(other->_0[2]);
    ensures other->_0[2] == old(other->_0[2]);
    ensures words->_0[3] == old(words->_0[3]) + old(other->_0[3]);
    ensures other->_0[3] == old(other->_0[3]);
} by { execute(); simp(); }

uint32 local(uint32 a, uint32 b) { requires a == 6u32; requires b == 2u32; ensures result == ((a * 2u32 % 7u32) ^ (b * 2u32 % 7u32)); } by { execute(); simp(); }
