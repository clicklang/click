# Original constructor contracts shared by the public checksum boundaries.
struct __rust_q_I6_adler2_I7_Adler32 __rust_q_I6_adler2_I7_Adler32_default() {
 ensures result.a == 1;
 ensures result.b == 0;
} by { execute(); simp(); }

struct __rust_q_I6_adler2_I7_Adler32 __rust_q_I6_adler2_T29___rust_q_I6_adler2_I7_Adler32_I3_new() {
 ensures result.a == 1;
 ensures result.b == 0;
} by { execute(); simp(); }

