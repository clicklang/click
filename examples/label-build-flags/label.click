import click::bytes;
import click::cstr;

verifying "label_fit.c";
verifying "label_copy.c";

uint64 label_fit(uint64 length) {
    ensures result < 32;
    ensures result <= length;
    ensures length < 32u64 implies result == length;
    ensures 32u64 <= length implies result == 31u64;
} by auto();

uint64 label_measure(const char* src) {
    let n: uint64;
    views cstr_at(src, n);
    ensures n < 32u64 implies result == n;
    ensures 32u64 <= n implies result == 31u64;
} by auto();

uint64 label_copy(char* dst, const char* src) {
    let len: uint64;
    views cstr_at(src, len);
    owns dst[0u64..32u64];
    requires separate(memory(dst[0u64..32u64]), memory(src[0u64..len + 1u64]));
    ensures len < 32u64 implies result == len;
    ensures 32u64 <= len implies result == 31u64;
    ensures dst[result] == '\0';
    ensures bytes::equal(dst, 0u64, src, 0u64, result);
} by {
    step();
    step();
    step();
    open(cstr_at(src, len)) {
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
