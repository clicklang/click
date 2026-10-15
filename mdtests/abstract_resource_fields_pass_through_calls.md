# An abstract resource's fields pass through calls

An abstract resource may declare fields. Its instances carry them, but it has
no body: no proof folds, unfolds, or observes one, so only a contract produces
or consumes an instance. Here trusted `pack` and `unpack` turn the cell at
`sq` into an `obj` whose `size` is its value and back, and `total` and
`area` know the object only by `size`. The caller binds the instance
`pack` produces and recovers the cell's value when `unpack` consumes it.

```c filename=abstract_resource_fields_pass_through_calls.c
void pack(int32* p);
void unpack(int32* p);
int32 area(int32* self, int32 scale);
int32 total(int32* s, int32 scale) { return area(s, scale); }
int32 caller(int32* sq, int32 scale) { pack(sq); int32 r = total(sq, scale); unpack(sq); return r; }
```

```click
verifying "abstract_resource_fields_pass_through_calls.c";
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
    let { o: q } = step(pack(sq), {});
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
pass
```
