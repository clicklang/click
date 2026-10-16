import click::bytes;
import click::cstr;

verifying "label_fit.c";
verifying "label_copy.c";

uint64 label_fit(uint64 length) {
    ensures result < 32;
    ensures result <= length;
    ensures length < 32u64 implies result == length;
    ensures 32u64 <= length implies result == 31u64;
} by auto;

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
    ensures bytes::equal(dst, 0u64, src, 0u64, result);
} by {
    step();
    step();
    step();
    open(cstr_at(src, s.len)) {
        unfold(bytes::equal);
        step();
        mark copied;
        step();
        have bytes::equal(dst, 0u64, src, 0u64, n) by {
            transport(
                at(copied, (0u64..n).all(|k| {
                    ((uint8*)dst)[0u64 + k] == old(((uint8*)src)[0u64 + k])
                })),
                (0u64..n).all(|k| { ((uint8*)dst)[0u64 + k] == ((uint8*)src)[0u64 + k] })
            );
        }
        execute();
    }
}
