# Select one translation-unit-local helper
```c filename=first.c
static inline int helper(void) { return 1; }
int first_use(void) { return helper(); }
```
```c filename=second.c
static inline int helper(void) { return 2; }
int second_use(void) { return helper(); }
```
```click
verifying "first.c" as first;
verifying "second.c" as second;
int32 helper() {
    ensures result == 1;
} by { execute(); simp(); }
int32 second::helper() {
    ensures result == 2;
} by { execute(); simp(); }
int32 first_use() { ensures result == 1; } by { execute(); simp(); }
int32 second_use() { ensures result == 2; } by { execute(); simp(); }
```
```expect
fail: has multiple translation-unit-local definitions
```
