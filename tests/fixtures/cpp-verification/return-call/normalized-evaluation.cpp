int echo(int value) noexcept { return value; }
long echo64(long value) noexcept { return value; }
unsigned echo_u32(unsigned value) noexcept { return value; }
unsigned long echo_u64(unsigned long value) noexcept { return value; }
int first(int value, int sibling) noexcept { return value; }
int direct(int value, int sibling) noexcept { return first(echo(value), sibling); }
int initialized(int value, int sibling) noexcept {
    int captured = first(echo(value), sibling);
    return captured;
}
long initialized64(long value) noexcept { long captured = echo64(echo64(value)); return captured; }
unsigned initialized_u32(unsigned value) noexcept { unsigned captured = echo_u32(echo_u32(value)); return captured; }
unsigned long initialized_u64(unsigned long value) noexcept { unsigned long captured = echo_u64(echo_u64(value)); return captured; }
int discarded(int value) noexcept { echo(echo(value)); return value; }
struct Restore {
    int* slot;
    int saved;
    explicit Restore(int* value) noexcept : slot(value), saved(*value) { *slot = 7; }
    ~Restore() noexcept { *slot = saved; }
};
int read(int* slot) noexcept { return *slot; }
int initialized_cleanup(int& value) noexcept {
    Restore guard(&value);
    int captured = echo(read(&value));
    return captured;
}
struct Helper {
    static int echo(int value) noexcept { return value; }
    static int initialized(int value) noexcept { int captured = echo(echo(value)); return captured; }
};
