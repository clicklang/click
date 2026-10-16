import click::cstr;
import click::machine_integer;

verifying "label_fit.c";
verifying "label_copy.c";

uint64 label_fit(uint64 length) {
    ensures result < 32;
    ensures result <= length;
    ensures length < 32u64 implies result == length;
    ensures 32u64 <= length implies result == 31u64;
} by {
    if length < 32u64 {
        execute();
        have 32u64 <= length implies result == 31u64 by {
            intro();
            apply(uint64_less_equal_less_than_transitive(32u64, length, 32u64));
            contradiction(32u64 < 32u64);
        }
        simp();
    } else {
        execute();
        have result <= length by auto;
        have length < 32u64 implies result == length by {
            intro();
            contradiction(length < 32u64);
        }
        simp();
    }
}

uint64 label_measure(const char* src) {
    views s: cstr_at(src, _);
    ensures s.len < 32u64 implies result == s.len;
    ensures 32u64 <= s.len implies result == 31u64;
} by auto;

uint64 label_copy(char* dst, const char* src) {
    views s: cstr_at(src, _);
    owns dst[0u64..32u64];
    requires separate(memory(dst[0u64..32u64]), memory(src[0u64..s.len + 1u64]));
    ensures s.len < 32u64 implies result == s.len;
    ensures 32u64 <= s.len implies result == 31u64;
    ensures dst[result] == '\0';
} by {
    step();
    step();
    step();
    open(cstr_at(src, s.len)) {
        execute();
    }
}
