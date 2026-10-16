# An abstract resource cannot be folded

An abstract resource's instances carry fields but no body, so a proof cannot
fold one from the memory it describes, or with fields of its choosing: only a
contract produces an instance.

```c filename=abstract_resource_fields_cannot_be_folded.c
void pack(int32* p);
void unpack(int32* p);
int32 area(int32* self, int32 scale);
int32 total(int32* s, int32 scale) { return area(s, scale); }
int32 caller(int32* sq, int32 scale) { int32 r = total(sq, scale); unpack(sq); return r; }
```

```click
verifying "abstract_resource_fields_cannot_be_folded.c";
abstract resource obj(p: int32*) {
    field size: int32;
}
extern void pack(int32* p) {
    consumes p[0..1];
    produces o: obj(p);
    ensures o.size == old(p[0]);
}
extern void unpack(int32* p) {
    consumes o: obj(p);
    produces p[0..1];
    ensures p[0] == old(o.size);
}
int32 total(int32* s, int32 scale) {
    owns o: obj(s);
    requires 0 <= o.size and o.size <= 100;
    requires 0 <= scale and scale <= 100;
    ensures o.size == old(o.size);
    ensures result == o.size + scale;
} by { execute(); simp(); }
int32 caller(int32* sq, int32 scale) {
    owns sq[0..1];
    requires 0 <= sq[0] and sq[0] <= 100;
    requires 0 <= scale and scale <= 100;
    ensures sq[0] == old(sq[0]);
    ensures result == sq[0] + scale;
} by {
    let o = fold(obj(sq), { size: 5 });
    execute();
    simp();
}
extern int32 area(int32* self, int32 scale) {
    owns o: obj(self);
    requires 0 <= o.size and o.size <= 100;
    requires 0 <= scale and scale <= 100;
    ensures o.size == old(o.size);
    ensures result == o.size + scale;
}
```

```expect
fail: `obj` is an abstract resource
```
