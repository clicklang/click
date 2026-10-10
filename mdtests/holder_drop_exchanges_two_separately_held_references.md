# A two-for-one reference exchange accepts separately held units

`holder_drop` replaces the child control it consumes and exchanges two
references to `h->kid` for one, so its contract is a same-population quantity
exchange rather than a single-member effect. The caller holds one reference
from its own contract and a second one produced by `child_retain`, as two
separate facts, and names the child as `kid` while the callee names it
through `h->kid`. The call must admit the control as a companion of the
exchange and locate the two units as one population held in separate facts.
This catches a call that requires the requested quantity in one fact, or that
refuses a control companion beside a quantity exchange.

```c filename=holder_reference_exchange.c
struct child { int32 refs; };
struct holder { struct child* kid; };
void child_retain(struct child* obj) { obj->refs = obj->refs + 1; }
void child_release(struct child* obj) { obj->refs = obj->refs - 1; }
void holder_drop(struct holder* h) { child_release(h->kid); }
void share_then_drop(struct holder* h, struct child* kid) {
    child_retain(kid);
    holder_drop(h);
}
```

```click
authorized resource child_ref(obj: struct child*) {}
resource child_control(obj: struct child*) {
    owns *obj;
    owns authority(child_ref(obj));
    fact obj->refs == count(child_ref(obj));
}
verifying "holder_reference_exchange.c";
void child_retain(struct child* obj) {
    requires count(child_ref(obj)) < 2147483647;
    owns child_control(obj);
    produces child_ref(obj);
} by {
    unfold(child_control(obj));
    step();
    fold(child_ref(obj));
    fold(child_control(obj));
    execute();
    simp();
}
void child_release(struct child* obj) {
    requires 1 < count(child_ref(obj));
    owns child_control(obj);
    consumes child_ref(obj);
} by {
    unfold(child_control(obj));
    unfold(child_ref(obj));
    have 1 < obj->refs;
    have obj->refs - 1 >= 1 by {
        apply(int32_above_one_predecessor_is_at_least_one(obj->refs)) using { 1 < obj->refs; }
    }
    step();
    fold(child_control(obj));
    execute();
    simp();
}
void holder_drop(struct holder* h) {
    owns h->kid;
    consumes child_control(h->kid);
    produces child_control(old(h->kid));
    consumes 2 of child_ref(h->kid);
    produces child_ref(old(h->kid));
} by {
    have 2 <= count(child_ref(h->kid));
    have count(child_ref(h->kid)) > 1 by {
        simp() using { 2 <= count(child_ref(h->kid)); }
    }
    execute();
    simp();
}
void share_then_drop(struct holder* h, struct child* kid) {
    requires count(child_ref(kid)) < 2147483647;
    owns h->kid;
    requires h->kid == kid;
    owns child_control(kid);
    owns child_ref(kid);
} by {
    execute();
    simp();
}
```

```expect
pass
```
