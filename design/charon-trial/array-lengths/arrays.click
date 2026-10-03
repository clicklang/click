verifying "arrays.rs";

uint8 read(const uint8* bytes, uint64 index) {
    requires index < 4u64;
    views bytes[0..4];
    ensures result == bytes[(int32)index];
} by { execute(); simp(); }

void write(uint32* words, uint64 index, uint32 value) {
    requires index < 3u64;
    owns words[(int32)index..(int32)index + 1];
    ensures words[(int32)index] == value;
} by { execute(); simp(); }

int32 signed(const int32* values, uint64 index) {
    requires index < 2u64;
    views values[0..2];
    ensures result == values[(int32)index];
} by { execute(); simp(); }

uint64 length(const uint32* words) {
    ensures result == 3u64;
} by { execute(); simp(); }

uint64 empty(const uint8* bytes) {
    ensures result == 0u64;
} by { execute(); simp(); }

uint8 first(const uint8* bytes) {
    views bytes[0..4];
    ensures result == bytes[0];
} by { execute(); simp(); }

void update(uint32* words) {
    owns words[0..3];
    ensures words[1] == 7u32;
    ensures words[2] == 9u32;
    ensures words[0] == old(words[0]);
} by { execute(); simp(); }
