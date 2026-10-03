struct Box { int value; int other; };
int echo(int value) noexcept { return value; }
int first(int a, int b, int c) noexcept { return a; }
int second(int a, int b, int c) noexcept { return b; }
int third(int a, int b, int c) noexcept { return c; }
int field_first(const Box& box) noexcept { return first(echo(box.value), box.other, 0); }
int field_second(const Box& box) noexcept { return second(box.other, echo(box.value), 0); }
int field_third(const Box& box) noexcept { return third(box.other, 0, echo(box.value)); }
int field_initializer(const Box& box) noexcept { int value = second(echo(box.value), box.other, 0); return value; }
int field_discarded(const Box& box) noexcept { first(echo(box.value), box.other, 0); return box.other; }
int field_cast(const Box& box) noexcept { return second(echo(box.value), int(bool(box.other)), 0); }
