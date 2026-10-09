# Readable byte views follow a stated pointer equality

Byte-pointer parameters use the shared external-address block. Their equality
is a same-block offset equality, which must rewrite a readable-view address
just as a distinct-block pointer equality does. The rewrite retains the memory
snapshot and byte extent; the equality supplies no read authority by itself.

```c filename=alias-view.c
int32 f(const uint8* bytes, const uint8* cursor) { return 0; }
int32 shifted(const uint8* bytes, const uint8* cursor) { return 0; }
```

```click
verifying "alias-view.c";
int32 f(const uint8* bytes, const uint8* cursor) {
 views bytes[0..4]; requires cursor == bytes; ensures result == 0;
} by {
 have viewable(cursor[0..4]) by { rewrite(cursor == bytes); simp(); }
 execute(); simp();
}
int32 shifted(const uint8* bytes, const uint8* cursor) {
 views bytes[0..8]; requires cursor == bytes + 2; ensures result == 0;
} by {
 have viewable(bytes[2..6]) by { transport(viewable(bytes[0..8]),viewable(bytes[2..6])) using { viewable(bytes[0..8]); 0 <= 2; 2 <= 6; 6 <= 8; } }
 have viewable(cursor[0..4]) by { rewrite(cursor == bytes + 2); assumption(); }
 execute(); simp();
}
```

```expect
pass
```
