# A C++ uint32 equality above INT32_MAX is one fact with its int32 word

As for C
(`a_uint32_equality_above_int32_max_is_one_fact_with_its_int32_word.md`): a
C++ `unsigned int` equality is filed at `uint32` (rule K6), stated and used
as itself, and `static_cast<int>(u) == -1` reads the same word's fact.

```cpp filename=equality.cpp function=is_max;signed_view;stated profile=normal_only
int is_max(unsigned int u) noexcept { return u == 4294967295u; }
int signed_view(unsigned int u) noexcept { return static_cast<int>(u) == -1; }
unsigned int stated(unsigned int u) noexcept { return u; }
```

```click
verifying "equality.cpp";
int is_max(unsigned int u) {
    requires u == 4294967295u32;
    ensures result == 1;
} by { execute(); solve(); }
int signed_view(unsigned int u) {
    requires u == 4294967295u32;
    ensures result == 1;
} by { execute(); solve(); }
unsigned int stated(unsigned int u) {
    requires u == 4294967295u32;
    ensures result == 4294967295u32;
} by { execute(); solve(); }
```

```expect
pass
```
