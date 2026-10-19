# A loop ranking proof uses its counter bounds

```c filename=many.c
int32 caller() {
 int32 i;
 int32 v0;
 int32 v1;
 int32 v2;
 int32 v3;
 i = 0;
 v0 = 0;
 v1 = 0;
 v2 = 0;
 v3 = 0;
 while (i < 4) {
 v0 = v0 + 1;
 v1 = v1 + 1;
 v2 = v2 + 1;
 v3 = v3 + 1;
 i = i + 1;
 }
 return i;
}
```

```click
verifying "many.c";
int32 caller() { ensures result == 4; } by {
 step();
 step();
 step();
 step();
 step();
 step();
 step();
 step();
 step();
 step();
 loop { decreases 4 - i; invariant i >= 0; invariant i <= 4; invariant v0 == i; invariant v1 == i; invariant v2 == i; invariant v3 == i; }
 step(); simp();
}
```

```expect
pass
```
