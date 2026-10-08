# Checked paths past unreachable owned loops retain termination evidence

Neither loop is reachable under its function's precondition. The owned cell
adds an inherited frame check to the source loop; that annotation must not
make an exact returning execution look like an unranked loop summary.

```c filename=unreachable_owned_loops_terminate.c
int skip_while(int flag, int *p) {
    if (flag) { while (flag) { *p = 1; } }
    return 0;
}
int skip_do_while(int flag, int *p) {
    if (flag) { do { *p = 1; } while (flag); }
    return 0;
}
```

```click
verifying "unreachable_owned_loops_terminate.c";
int32 skip_while(int32 flag, int32* p) {
    requires flag == 0;
    owns p[0..1];
    ensures result == 0;
} by { execute(); simp(); }
int32 skip_do_while(int32 flag, int32* p) {
    requires flag == 0;
    owns p[0..1];
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
pass
```
