verifying "snapshots.rs";
uint32 computed_move(uint32 a, uint32 b) {
    ensures result == b ^ 1u32;
} by { execute(); simp(); }
uint32 source_write(uint32 a, uint32 b) {
    ensures result == a;
} by { execute(); simp(); }
uint32 target_write(uint32 a, uint32 b) {
    ensures result == b;
} by { execute(); simp(); }
uint32 replacement(uint32 a, uint32 b) {
    ensures result == b;
} by { execute(); simp(); }
uint32 neighbors(uint32 a, uint32 b) {
    ensures result == 28u32;
} by { execute(); simp(); }
uint32 sparse(uint32 a, uint32 b) {
    ensures result == b;
} by { execute(); simp(); }
int32 signed(int32 a, int32 b) {
    ensures result == b;
} by { execute(); simp(); }
uint8 bytes(uint8 a, uint8 b) {
    ensures result == b;
} by { execute(); simp(); }
