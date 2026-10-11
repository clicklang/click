verifying "operators.rs";

impl MulAssign<u32> for U32X4 {
    fn mul_assign(&mut self, rhs: u32) {
        requires rhs == 0u32 or self.0[0] <= 4294967295u32 / rhs;
        requires rhs == 0u32 or self.0[1] <= 4294967295u32 / rhs;
        requires rhs == 0u32 or self.0[2] <= 4294967295u32 / rhs;
        requires rhs == 0u32 or self.0[3] <= 4294967295u32 / rhs;
        owns self.0[0..4];
        ensures self.0[0] == old(self.0[0]) * rhs;
        ensures self.0[1] == old(self.0[1]) * rhs;
        ensures self.0[2] == old(self.0[2]) * rhs;
        ensures self.0[3] == old(self.0[3]) * rhs;
    } by { execute(); simp(); }
}

fn scaled(words: &mut U32X4, factor: u32) {
    requires factor == 0u32 or words.0[0] <= 4294967295u32 / factor;
    requires factor == 0u32 or words.0[1] <= 4294967295u32 / factor;
    requires factor == 0u32 or words.0[2] <= 4294967295u32 / factor;
    requires factor == 0u32 or words.0[3] <= 4294967295u32 / factor;
    owns words.0[0..4];
    ensures words.0[0] == old(words.0[0]) * factor;
    ensures words.0[1] == old(words.0[1]) * factor;
    ensures words.0[2] == old(words.0[2]) * factor;
    ensures words.0[3] == old(words.0[3]) * factor;
} by { execute(); simp(); }

impl RemAssign<u32> for U32X4 {
    fn rem_assign(&mut self, quotient: u32) {
        requires quotient != 0u32;
        owns self.0[0..4];
        ensures self.0[0] == old(self.0[0]) % quotient;
        ensures self.0[1] == old(self.0[1]) % quotient;
        ensures self.0[2] == old(self.0[2]) % quotient;
        ensures self.0[3] == old(self.0[3]) % quotient;
    } by { execute(); simp(); }
}

fn reduced(words: &mut U32X4, divisor: u32) {
    requires divisor != 0u32;
    owns words.0[0..4];
    ensures words.0[0] == old(words.0[0]) % divisor;
    ensures words.0[1] == old(words.0[1]) % divisor;
    ensures words.0[2] == old(words.0[2]) % divisor;
    ensures words.0[3] == old(words.0[3]) % divisor;
} by { execute(); simp(); }

impl AddAssign<&U32X4> for U32X4 {
    fn add_assign(&mut self, other: &U32X4) {
        requires separate(memory(self.0[0..4]), memory(other.0[0..4]));
        views other.0[0..4];
        requires self.0[0] <= 1000u32;
        requires other.0[0] <= 1000u32;
        requires self.0[1] <= 1000u32;
        requires other.0[1] <= 1000u32;
        requires self.0[2] <= 1000u32;
        requires other.0[2] <= 1000u32;
        requires self.0[3] <= 1000u32;
        requires other.0[3] <= 1000u32;
        owns self.0[0..4];
        ensures self.0[0] == old(self.0[0]) + old(other.0[0]);
        ensures other.0[0] == old(other.0[0]);
        ensures self.0[1] == old(self.0[1]) + old(other.0[1]);
        ensures other.0[1] == old(other.0[1]);
        ensures self.0[2] == old(self.0[2]) + old(other.0[2]);
        ensures other.0[2] == old(other.0[2]);
        ensures self.0[3] == old(self.0[3]) + old(other.0[3]);
        ensures other.0[3] == old(other.0[3]);
    } by { execute(); simp(); }
}

fn added(words: &mut U32X4, other: &U32X4) {
    requires separate(memory(words.0[0..4]), memory(other.0[0..4]));
    views other.0[0..4];
    requires words.0[0] <= 1000u32;
    requires other.0[0] <= 1000u32;
    requires words.0[1] <= 1000u32;
    requires other.0[1] <= 1000u32;
    requires words.0[2] <= 1000u32;
    requires other.0[2] <= 1000u32;
    requires words.0[3] <= 1000u32;
    requires other.0[3] <= 1000u32;
    owns words.0[0..4];
    ensures words.0[0] == old(words.0[0]) + old(other.0[0]);
    ensures other.0[0] == old(other.0[0]);
    ensures words.0[1] == old(words.0[1]) + old(other.0[1]);
    ensures other.0[1] == old(other.0[1]);
    ensures words.0[2] == old(words.0[2]) + old(other.0[2]);
    ensures other.0[2] == old(other.0[2]);
    ensures words.0[3] == old(words.0[3]) + old(other.0[3]);
    ensures other.0[3] == old(other.0[3]);
} by { execute(); simp(); }

fn local(a: u32, b: u32) -> u32 { requires a <= 1000u32; requires b <= 1000u32; ensures result == ((a * 2u32 % 7u32) ^ (b * 2u32 % 7u32)); } by { execute(); simp(); }
