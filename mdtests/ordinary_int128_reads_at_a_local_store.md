# Ordinary 128-bit reads name the writes to their own objects

A disjoint store preserves a typed 128-bit read of an address-backed local.
The same rule applies whether the local is signed or unsigned.

```cpp filename=wide_reads.cpp function=read_signed;read_unsigned profile=normal_only
__int128 read_signed(__int128 value) noexcept {
    __int128 slot = 0;
    int other = 0;
    slot = value;
    other = 1;
    return slot;
}

unsigned __int128 read_unsigned(unsigned __int128 value) noexcept {
    unsigned __int128 slot = 0;
    int other = 0;
    slot = value;
    other = 1;
    return slot;
}
```

```click
verifying "wide_reads.cpp";

int128 read_signed(int128 value) {
    ensures result == value;
} by {
    step();
    step();
    step();
    mark written;
    step();
    have *(&slot) == value by solve();
    have separate(memory(*(&other)), memory(*(&slot))) by known();
    have separate(region(3).footprint, memory(*(&slot))) by {
        solve() using { separate(memory(*(&other)), memory(*(&slot))); };
    }
    have *(&slot) == at(written, *(&slot)) by {
        preserve(memory(*(&slot)), region(3));
    }
    step_until(function.exit);
    solve();
}

uint128 read_unsigned(uint128 value) {
    ensures result == value;
} by {
    step();
    step();
    step();
    mark written;
    step();
    have *(&slot) == value by solve();
    have separate(memory(*(&other)), memory(*(&slot))) by known();
    have separate(region(3).footprint, memory(*(&slot))) by {
        solve() using { separate(memory(*(&other)), memory(*(&slot))); };
    }
    have *(&slot) == at(written, *(&slot)) by {
        preserve(memory(*(&slot)), region(3));
    }
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
