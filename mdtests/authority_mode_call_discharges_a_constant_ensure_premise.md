# A call discharges a constant ensure premise in authority mode

`choose` states each result as an implication on its selector argument. At a
call with a constant selector, lowering turns each premise into a constant
condition such as `0 == 0` or `1 == 0`. The call rule publishes an ensure's
consequent once its premise is settled. A closed constant premise settles
without the call context, under either resource semantics.

Authority mode used to accept only premises stated in the call context, so it
kept every ensure as an implication. A caller that read `result.value` then
had no fact for it.

```c filename=choose.c
struct pair {
    int32 value;
    int32 other;
};

struct pair choose(int32 choose_left, struct pair left, struct pair right) {
    return choose_left ? left : right;
}

int32 read_chosen() {
    struct pair left = {4, 5};
    struct pair right = {30, 40};
    struct pair chosen = choose(1, left, right);
    return chosen.value;
}
```

```click
verifying "choose.c";

struct pair choose(int32 choose_left, struct pair left, struct pair right) {
    ensures choose_left == 0 implies result.value == right.value;
    ensures choose_left != 0 implies result.value == left.value;
} by {
    auto;
}

int32 read_chosen() {
    ensures result == 4;
} by {
    execute();
    simp();
}
```

```expect
pass
```
