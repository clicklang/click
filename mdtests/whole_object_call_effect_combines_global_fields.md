# Whole-object global call effects
```c filename=pairs.c
struct pair { unsigned long left; unsigned long right; };
static struct pair state;
void set_pair(struct pair* p) { p->left = 1; p->right = 2; }
void caller(void) { set_pair(&state); }
```
```click
verifying "pairs.c" as unit;
void set_pair(struct pair* p) { owns *p; } by { execute(); simp(); }
void caller() {
    owns unit::state.left;
    owns unit::state.right;
} by { execute(); simp(); }
```
```expect
pass
```
