# Floating arithmetic keeps its C meaning under Integer arithmetic

Under `arithmetic "integer";` a comparison that does arithmetic compares exact
Integers, except where an arithmetic operand has only a C meaning. A
floating-point value is such an operand: it has no Integer observation, so
`old(obj->value) * scale` is the C product, as it is without the directive.
The function is the jsonc-numeric example's `json_object_scale_double`.

```c filename=scale_double.c
struct json_object {
    double value;
};

double json_object_scale_double(struct json_object *obj, int scale) {
    obj->value = obj->value * scale;
    return obj->value;
}
```

```click
arithmetic "integer";
verifying "scale_double.c";

double json_object_scale_double(struct json_object* obj, int32 scale) {
    requires isfinite(obj->value);
    requires isfinite(obj->value * scale);
    consumes obj->value;

    ensures returns_scaled: result == old(obj->value) * scale;
    ensures stores_scaled: obj->value == old(obj->value) * scale;
} by auto();
```

```expect
pass
```
