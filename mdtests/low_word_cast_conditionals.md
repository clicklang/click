# Low-word casts in conditional arms preserve the destination interpretation

```click
theorem low_word_casts_keep_their_destination(flag: Bool, w: uint64) {
    requires w == 8589934591u64;
    ensures flag implies (if flag { w as int32 } else { 3 }) == -1 by {
        intro();
        rewrite(w, 8589934591u64);
        close() using { flag; };
    }
    ensures (not flag) implies (if flag { 3u32 } else { w as uint32 }) == 4294967295u32 by {
        intro();
        rewrite(w, 8589934591u64);
        close() using { not flag; };
    }
}
```

```expect
pass
```
