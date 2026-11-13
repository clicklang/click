# Common call arguments preserve a selected length equality

```click
import click::rust::vec;
theorem selected_index(a: Vec<uint32>, b: Vec<uint32>, c: Vec<uint32>, y: uint32) {
    requires vec::len(a) == 0u64;
    requires to_integer(vec::len(b)) == to_integer(vec::len(a)) + 1;
    requires vec::get(c, vec::len(b)) == y;
    ensures vec::get(c, 1u64) == y by {
        have vec::len(b) == 1u64 by {
            solve() using { vec::len(a) == 0u64; to_integer(vec::len(b)) == to_integer(vec::len(a)) + 1; }
        }
        rewrite(1u64 == vec::len(b));
        assumption();
    }
}

theorem implicit_index(a: Vec<uint32>, b: Vec<uint32>, c: Vec<uint32>, y: uint32) {
    requires vec::len(a) == 0u64;
    requires to_integer(vec::len(b)) == to_integer(vec::len(a)) + 1;
    requires vec::get(c, vec::len(b)) == y;
    ensures vec::get(c, 1u64) == y;
}

```

```expect
pass
```
