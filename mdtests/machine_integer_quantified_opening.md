# Opening machine existentials preserves the exact types

```click
theorem opened_wide() {
    requires exists (x: int64) { x == 4294967296i64 };
    ensures exists (y: int64) { y == 4294967296i64 } by {
        let candidate = obtain(exists (candidate: int64) { candidate == 4294967296i64 });
        witness(candidate);
        solve();
    }
}

theorem opened_byte() {
    requires exists (x: uint8) { x == 'a' };
    ensures exists (y: uint8) { y == 'a' } by {
        let candidate = obtain(exists (candidate: uint8) { candidate == 'a' });
        witness(candidate);
        solve();
    }
}
```

```expect
pass
```
