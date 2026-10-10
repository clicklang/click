target "x86_64-linux-userspace";
verifying "adler32.c";
uint64 adler32_z(uint64 adler, const uint8* buf, uint64 len) {
 requires adler == 1u64;
 requires len == 0u64;
 requires buf != 0;
 ensures result == 1u64;
} by { execute(); simp(); }
