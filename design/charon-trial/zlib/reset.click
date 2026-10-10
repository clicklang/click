target "x86_64-linux-userspace";
verifying "adler32.c";
uint64 adler32_z(uint64 adler, const uint8* buf, uint64 len) {
 requires buf == 0;
 requires len != 1u64;
 ensures result == 1u64;
} by { execute(); simp(); }
