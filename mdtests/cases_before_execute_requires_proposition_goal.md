# Execution-level cases requires a focused proposition goal
```c filename=cases.c
int32 f(int32 n) { return n; }
```
```click
verifying "cases.c";
int32 f(int32 n) {
 requires n == 0 or n == 1;
 ensures result <= 1;
 ensures result >= 0;
} by {

 cases {
  n == 0 => { have n <= 1 by normalize(); }
  n == 1 => { have n <= 1 by normalize(); }
 }
execute();
 simp();
}
```
```expect
fail: `cases` requires a focused proposition goal
```
