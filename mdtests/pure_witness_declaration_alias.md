# Pure witnesses capture declaration-level aliases

```click
theorem retain(p: int32*) {
    let saved = p;
    ensures exists (q: int32*) { q == saved } by {
        witness { q: saved };
        solve();
    }
}

theorem capture_outer(n: int32) {
    let saved = n;
    ensures forall (n: int32) { exists (q: int32) { q == saved } } by {
        intro();
        witness { q: saved };
        solve();
    }
}
```

```expect
pass
```
