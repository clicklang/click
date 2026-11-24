# Readable byte views follow a stated pointer equality

Byte-pointer parameters use the shared external-address block. Their equality
is a same-block offset equality, which must rewrite a readable-view address
just as a distinct-block pointer equality does. The rewrite retains the memory
state and byte span; the equality supplies no read authority by itself.

```c filename=alias-view.c
int32 f(const uint8* bytes, const uint8* cursor) { return 0; }
int32 shifted(const uint8* bytes, const uint8* cursor) { return 0; }
```

```click
verifying "alias-view.c";
int32 f(const uint8* bytes, const uint8* cursor) {
 views bytes[0..4]; requires cursor == bytes; ensures result == 0;
} by {
 have viewable(cursor[0..4]) by { rewrite(cursor, bytes); close(); }
}
int32 shifted(const uint8* bytes, const uint8* cursor) {
 views bytes[0..8]; requires cursor == bytes + 2; ensures result == 0;
} by {
 have viewable(bytes[2..6]) by { have viewable(bytes[2..6]) by {
     have viewable(bytes[0..8]) by {
         close();
     }
     have viewable(bytes[2..6]) by {
         have contains(memory(bytes[0..8]), memory(bytes[2..6])) by {
             apply(click::separation::contains_subrange(bytes, 0, 8, 2, 6));
         }
         apply(click::separation::viewable_restrict(memory(bytes[0..8]), memory(bytes[2..6])));
     }
     close();
 }
     close();
 }
 have viewable(cursor[0..4]) by { rewrite(cursor, bytes + 2); close(); }
}
```

```expect
pass
```
