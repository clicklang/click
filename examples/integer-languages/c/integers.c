// The cross-language integer fixture's programs (tests/examples/integer_languages.rs);
// integers.c, integers.cpp and integers.rs are the same functions.

#include <stdbool.h>

int add_i32(int a, int b) { return a + b; }
int sub_i32(int a, int b) { return a - b; }
int mul_i32(int a, int b) { return a * b; }

unsigned int wrapping_add_u32(unsigned int a, unsigned int b) { return a + b; }
unsigned int wrapping_sub_u32(unsigned int a, unsigned int b) { return a - b; }
unsigned int wrapping_mul_u32(unsigned int a, unsigned int b) { return a * b; }

unsigned int above_int32_max(void) { return 4000000000u; }
unsigned int keep_above_int32_max(unsigned int u) {
    if (u > 2147483647u) {
        return u;
    }
    return 0u;
}

int to_signed_i32(unsigned int u) { return (int)u; }
unsigned int to_unsigned_u32(int x) { return (unsigned int)x; }

unsigned int div_u32(unsigned int a, unsigned int b) { return a / b; }
unsigned int rem_u32(unsigned int a, unsigned int b) { return a % b; }
unsigned int shr_u32(unsigned int a, unsigned int n) { return a >> n; }
int div_i32(int a, int b) { return a / b; }
int rem_i32(int a, int b) { return a % b; }
int shr_i32(int a, unsigned int n) { return a >> n; }

unsigned char narrow_u8(unsigned int x) { return (unsigned char)x; }
signed char narrow_i8(int x) { return (signed char)x; }
unsigned char narrow_u8_in_range(unsigned int x) { return (unsigned char)x; }

long add_i64(long a, long b) { return a + b; }
unsigned long wrapping_add_u64(unsigned long a, unsigned long b) { return a + b; }

bool below_i32(int a, int b) { return a < b; }
bool below_u32(unsigned int a, unsigned int b) { return a < b; }
bool sign_bit_set(unsigned int u) { return (int)u < 0; }
