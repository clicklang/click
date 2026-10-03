verifying "external.rs";

void copy_small(uint32* target, const uint32* source) {
    owns target[0..8];
    views source[0..8];
    ensures target[0] == old(source[0]);
    ensures target[7] == old(source[7]);
} by { execute(); simp(); }

void fill_small(uint32* target, uint32 value) {
    owns target[0..8];
    ensures target[0] == value;
    ensures target[7] == value;
} by { execute(); simp(); }

void copy_medium(uint32* target, const uint32* source) {
    owns target[0..1024];
    views source[0..1024];
    ensures target[0] == old(source[0]);
    ensures target[1023] == old(source[1023]);
} by { execute(); simp(); }

void fill_medium(uint32* target, uint32 value) {
    owns target[0..1024];
    ensures target[0] == value;
    ensures target[1023] == value;
} by { execute(); simp(); }

void copy_million(uint32* target, const uint32* source) {
    owns target[0..1000000];
    views source[0..1000000];
    ensures target[0] == old(source[0]);
    ensures target[999999] == old(source[999999]);
} by { execute(); simp(); }

void fill_million(uint32* target, uint32 value) {
    owns target[0..1000000];
    ensures target[0] == value;
    ensures target[999999] == value;
} by { execute(); simp(); }

int32 independent(int32* source) { owns source[0..2]; ensures result == old(source[0]); ensures source[0] == 99; } by { execute(); simp(); }
void bytes(uint8* target, const uint8* source) { owns target[0..2]; views source[0..2]; ensures target[0] == old(source[0]); ensures target[1] == old(source[1]); } by { execute(); simp(); }
void empty(uint32* target, const uint32* source) { ensures 0u32 == 0u32; } by { execute(); simp(); }
