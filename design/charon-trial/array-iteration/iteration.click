verifying "iteration.rs";
uint32 borrowed(const uint32* words) {
    views words[0..4];
    ensures result == 4u32;
    ensures forall (k: int32) { 0 <= k and k < 4 implies words[k] == old(words[k]) };
} by { execute(); simp(); }
uint32 moved(uint32 a, uint32 b) {
    ensures result == (a ^ b);
} by { execute(); simp(); }
uint8 bytes(uint8 a, uint8 b) {
    ensures result == ((b ^ (a & 255)) & 255);
} by { execute(); simp(); }
uint32 explicit(const uint32* words) {
    views words[0..4];
    ensures result == 4u32;
} by { execute(); simp(); }
uint32 local(uint32 a, uint32 b) {
    ensures result == (a ^ b ^ 3u32 ^ 4u32);
} by { execute(); simp(); }
uint32 empty() {
    ensures result == 0u32;
} by { execute(); simp(); }
uint32 ordered(uint32 a, uint32 b) {
    ensures result == ((a << 1u32) ^ b);
} by { execute(); simp(); }

int32 signed(const int32* words) {
    views words[0..4];
    ensures result == old(words[0]);
    ensures words[3] == old(words[3]);
} by { execute(); simp(); }
