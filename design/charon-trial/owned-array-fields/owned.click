verifying "owned.rs";
uint32 construct(uint32 value, uint64 index) {
    requires index < 4u64;
    ensures result == value;
} by { execute(); simp(); }
uint32 moved(uint32 value, uint64 index) {
    requires index < 4u64;
    ensures result == value;
} by { execute(); simp(); }
uint32 reassigned(uint32 value, uint32 replacement) {
    ensures result == replacement;
} by { execute(); simp(); }
uint32 neighboring_fields(uint32 value, uint32 replacement) {
    ensures result == 28u32;
} by { execute(); simp(); }
uint32 extracted(uint32 value, uint64 index) {
    requires index < 4u64;
    ensures result == value;
} by { execute(); simp(); }
uint32 snapshot(uint32 value) {
    ensures result == value;
} by { execute(); simp(); }
uint32 tuple_move(uint32 value) {
    ensures result == value;
} by { execute(); simp(); }
uint8 byte_move(uint8 value) {
    ensures result == value;
} by { execute(); simp(); }
uint8 empty_move(uint8 value) {
    ensures result == 31u8;
} by { execute(); simp(); }
