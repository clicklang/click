import click::bytes;

void* memcpy(void* destination, const void* source, unsigned long bytes) {
    views (source as (const uint8*))[0..bytes];
    consumes uninitialized((destination as (uint8*))[0..bytes]);
    produces (destination as (uint8*))[0..bytes];
    ensures result == destination;
    ensures bytes::equal(destination as (uint8*), 0u64, old(source as (const uint8*)), 0u64, bytes);
}
