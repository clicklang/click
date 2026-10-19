# Each postcondition uses its own arithmetic bounds

```c filename=hunt.c
int32 caller(int32 x) { return x; }
```

```click
verifying "hunt.c";
int32 caller(int32 x) {
 requires 0 <= x;
 requires x <= 1000;
 ensures result >= x - 0;
 ensures result >= x - 1;
 ensures result >= x - 2;
 ensures result >= x - 3;
 ensures result >= x - 4;
 ensures result >= x - 5;
 ensures result >= x - 6;
 ensures result >= x - 7;
 ensures result >= x - 8;
 ensures result >= x - 9;
 ensures result >= x - 10;
 ensures result >= x - 11;
 ensures result >= x - 12;
 ensures result >= x - 13;
 ensures result >= x - 14;
 ensures result >= x - 15;
} by { step(); simp(); }
```

```expect
pass
```
