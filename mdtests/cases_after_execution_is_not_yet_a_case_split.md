# `cases` after execution is not yet a case split

At an execution frontier `cases` splits the proof; after execution it is not
yet supported as a split, and the refusal says where to write it instead.
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
execute();
 cases {
  n == 0 => { have n <= 1 by normalize(); }
  n == 1 => { have n <= 1 by normalize(); }
 }

 simp();
}
```
```expect
fail: `cases` after execution is not supported yet
```
