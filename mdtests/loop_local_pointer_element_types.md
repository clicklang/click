# Local pointers retain their element types in loop invariants

A byte pointer local has one-byte elements. A uint64 pointer local has
eight-byte elements. Loop invariant lowering retains the declared types,
just as a frontier `have` does; a fallback to int32 elements would demand too
much byte authority and too little uint64 authority.

```c filename=one-view.c
int32 f(const uint8* bytes) { const uint8* chunk = bytes; int32 inner = 1; while (inner > 0) { inner -= 1; } return 0; }
int32 wide(const uint64* bytes) { const uint64* chunk = bytes; int32 inner = 1; while (inner > 0) { inner -= 1; } return 0; }
```

```click
verifying "one-view.c";
int32 f(const uint8* bytes) { views bytes[0..4]; ensures result == 0; } by {
 execute_until(loop(0));
 have chunk == bytes;
 have viewable(bytes[0..4]) by { transport(at(function.entry,viewable(bytes[0..4])),viewable(bytes[0..4])) using { at(function.entry,viewable(bytes[0..4])); 0 <= 4; } }
 have viewable(chunk[0..4]) by { rewrite(chunk == bytes); assumption(); }
 loop {
 decreases inner;
 views chunk[0..4];
 invariant viewable(chunk[0..4]);
 invariant 0 <= inner and inner <= 1;
 invariant bytes == old(bytes);
 invariant chunk == bytes;
 preserve by { mark inner_head; step();
 have viewable(chunk[0..4]) by { transport(at(inner_head,viewable(chunk[0..4])),viewable(chunk[0..4])) using { at(inner_head,viewable(chunk[0..4])); 0 <= 4; } }
 close_invariants by { simp(); } }
 }
 execute(); simp();
}

int32 wide(const uint64* bytes) { views bytes[0..4]; ensures result == 0; } by {
 execute_until(loop(0));
 have chunk == bytes;
 have viewable(bytes[0..4]) by { transport(at(function.entry,viewable(bytes[0..4])),viewable(bytes[0..4])) using { at(function.entry,viewable(bytes[0..4])); 0 <= 4; } }
 have viewable(chunk[0..4]) by { rewrite(chunk == bytes); assumption(); }
 loop {
 decreases inner;
 views chunk[0..4];
 invariant viewable(chunk[0..4]);
 invariant 0 <= inner and inner <= 1;
 invariant bytes == old(bytes);
 invariant chunk == bytes;
 preserve by { mark inner_head; step();
 have viewable(chunk[0..4]) by { transport(at(inner_head,viewable(chunk[0..4])),viewable(chunk[0..4])) using { at(inner_head,viewable(chunk[0..4])); 0 <= 4; } }
 close_invariants by { simp(); } }
 }
 execute(); simp();
}
```

```expect
pass
```
