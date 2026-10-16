import click::bytes;
import click::cstr;

// The C library's byte functions, with C's `size_t` counts. C converts
// `memset`'s `int` fill value to `unsigned char`; Click models that narrowing
// only for a representable value, so the value is required to be one.
extern uint8* memcpy(uint8 destination[], const uint8 source[], uint64 bytes) {
    views source[0..bytes];
    owns destination[0..bytes];
    ensures result == destination;
    ensures bytes::equal(destination, 0u64, old(source), 0u64, bytes);
}

extern int32 memcmp(const uint8 left[], const uint8 right[], uint64 bytes) {
    views left[0..bytes];
    views right[0..bytes];
    requires forall (k: uint64) { k < bytes implies defined(left[k]) and defined(right[k]) };
    ensures result == 0 implies bytes::equal(left, 0u64, right, 0u64, bytes);
    ensures result != 0 implies not bytes::equal(left, 0u64, right, 0u64, bytes);
}

extern uint8* memset(uint8 destination[], int32 value, uint64 bytes) {
    requires 0 <= value;
    requires value <= 255;
    owns destination[0..bytes];
    ensures result == destination;
    ensures (0u64..bytes).all(|k| {
        defined(destination[k]) and destination[k] == value
    });
}

extern uint64 strlen(const uint8* bytes) {
    views s: cstr_at(bytes, _);
    ensures result == s.len;
}
