# One helper input does not imply a population total of one

Other owners may retain members outside the helper's contract.

```c filename=wildcard_helper_arbitrary_total.c
void inspect(int32* pool, int32* member) {}
```

```click resource_semantics=authority
authorized resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_helper_arbitrary_total.c";
void inspect(int32* pool, int32* member) {
    owns authority(slot(pool, _));
    owns slot(pool, member);
    ensures count(slot(pool, _)) == 1;
} by { execute(); simp(); }
```

```expect
fail: unclosed goal: count(slot(pool, _)) == 1
```
