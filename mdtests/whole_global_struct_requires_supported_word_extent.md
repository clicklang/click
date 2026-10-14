# A whole global object has the same supported extent as a pointee object

```c filename=small.c
struct small { char first; char second; char third; };
static struct small state;
void keep() {}
```
```click
verifying "small.c";
void keep() { owns state; } by { execute(); simp(); }
```
```expect
fail: a whole object cannot represent the 3-byte `struct small`
```
