# Pointer stores preserve return facts

Resolving stored symbolic pointers must preserve the comparisons used by
`assumption()`, rather than replace their goals with an unrecorded literal truth.

```c filename=store.c
struct pair { int32 *left; int32 *right; };
void set(struct pair *owner, int32 *left, int32 *right) {
    owner->left = left;
    owner->right = right;
}
```
```click
verifying "store.c";
void set(struct pair* owner, int32* left, int32* right) {
    owns *owner;
    ensures owner->left == left;
    ensures owner->right == right;
} by {
    step(); step(); step();
    assumption(); assumption(); assumption();
}
```
```expect
pass
```
