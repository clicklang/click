```c filename=consume.c
void consume(int32* p) {}
```
```click resource_semantics=authority
authorized resource token(p: int32*) {}
verifying "consume.c";
void consume(int32* p) {
    owns authority(token(p));
    consumes token(p);
    ensures 1 <= count(token(p));
} by {
    have 0 < count(token(p)) by { arithmetic() using { 1 <= count(token(p)); } }
    apply(int32_positive_predecessor_is_nonnegative(count(token(p)))) using { 0 < count(token(p)); }
    unfold(token(p)); execute(); simp();
}
```
```expect
fail: ensures 1 <= count(token(p))
```
