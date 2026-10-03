# a population count across a `produces` transition

`produces object_ref(obj)` adds one checked member to the family. Owning one
member gives a lower bound, not an exact entry count. The post-state count is
therefore the arbitrary entry count plus one; a fixed postcondition of one
fails. The companion
[`population_count_states_its_transition.md`](population_count_states_its_transition.md)
states and proves the actual transition under the same authority protocol.

```c filename=population_count_across_a_produces_transition.c
void object_retain(int32* obj) {
}
```

```click resource_semantics=authority
resource object_ref(obj: int32*) {}

verifying "population_count_across_a_produces_transition.c";

void object_retain(int32* obj) {
    owns authority(object_ref(obj));
    owns object_ref(obj);
    requires count(object_ref(obj)) <= 1000;
    produces object_ref(obj);
    ensures count(object_ref(obj)) == 1;
} by {
    fold(object_ref(obj));
    execute();
    simp();
}
```

```expect
fail: ensures count(object_ref(obj)) == 1
```
