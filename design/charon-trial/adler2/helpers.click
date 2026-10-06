verifying "src/lib.rs";

struct __rust_q_I6_adler2_I4_algo_I5_U32X4 __rust_q_I6_adler2_I4_algo_T35___rust_q_I6_adler2_I4_algo_I5_U32X4_I4_from(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len >= 4u64;
    views bytes[0..4];
    ensures result._0[0] == bytes[0];
    ensures result._0[1] == bytes[1];
    ensures result._0[2] == bytes[2];
    ensures result._0[3] == bytes[3];
    ensures result._0[0] <= 255u32;
    ensures result._0[1] <= 255u32;
    ensures result._0[2] <= 255u32;
    ensures result._0[3] <= 255u32;
} by { execute(); simp(); }

void __rust_q_I6_adler2_I4_algo_I5_U32X4_add_assign_value_35__rust_q_I6_adler2_I4_algo_I5_U32X4(struct __rust_q_I6_adler2_I4_algo_I5_U32X4* self, struct __rust_q_I6_adler2_I4_algo_I5_U32X4 other) {
    requires ((int64)self->_0[0] + (int64)other._0[0]) <= 4294967295i64;
    requires ((int64)self->_0[1] + (int64)other._0[1]) <= 4294967295i64;
    requires ((int64)self->_0[2] + (int64)other._0[2]) <= 4294967295i64;
    requires ((int64)self->_0[3] + (int64)other._0[3]) <= 4294967295i64;
    owns self->_0[0..4];
    ensures self->_0[0] == old(self->_0[0]) + other._0[0];
    ensures self->_0[1] == old(self->_0[1]) + other._0[1];
    ensures self->_0[2] == old(self->_0[2]) + other._0[2];
    ensures self->_0[3] == old(self->_0[3]) + other._0[3];
} by { execute(); simp(); }

void __rust_q_I6_adler2_I4_algo_I5_U32X4_rem_assign_u32(struct __rust_q_I6_adler2_I4_algo_I5_U32X4* self, uint32 quotient) {
    requires quotient != 0u32;
    owns self->_0[0..4];
    ensures self->_0[0] == old(self->_0[0]) % quotient;
    ensures self->_0[1] == old(self->_0[1]) % quotient;
    ensures self->_0[2] == old(self->_0[2]) % quotient;
    ensures self->_0[3] == old(self->_0[3]) % quotient;
} by { execute(); simp(); }

void __rust_q_I6_adler2_I4_algo_I5_U32X4_mul_assign_u32(struct __rust_q_I6_adler2_I4_algo_I5_U32X4* self, uint32 rhs) {
    requires rhs == 0u32 or self->_0[0] <= 4294967295u32 / rhs;
    requires rhs == 0u32 or self->_0[1] <= 4294967295u32 / rhs;
    requires rhs == 0u32 or self->_0[2] <= 4294967295u32 / rhs;
    requires rhs == 0u32 or self->_0[3] <= 4294967295u32 / rhs;
    owns self->_0[0..4];
    ensures self->_0[0] == old(self->_0[0]) * rhs;
    ensures self->_0[1] == old(self->_0[1]) * rhs;
    ensures self->_0[2] == old(self->_0[2]) * rhs;
    ensures self->_0[3] == old(self->_0[3]) * rhs;
} by { execute(); simp(); }
