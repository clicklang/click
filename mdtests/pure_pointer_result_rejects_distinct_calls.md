# Distinct pointer-valued applications do not share a fresh result name

```click
function identity(p: int32*) -> int32* { p }
theorem separate(p: int32*, q: int32*) {
    requires identity(p) == 0;
    requires p != q;
    ensures identity(q) == 0 by assumption();
}
```
```expect
fail: assumption
```
