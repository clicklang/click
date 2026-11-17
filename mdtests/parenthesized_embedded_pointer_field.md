# Parenthesized embedded fields keep their declared layout

The parentheses introduced by a C++ model accessor must preserve the nested
record identity, including a pointer field's type and the region it reads.

```c filename=parenthesized_embedded_pointer_field.c
struct Inner { int* data; };
struct Outer { struct Inner inner; };
int first(struct Outer* object) { return object->inner.data[0]; }
```

```click
verifying "parenthesized_embedded_pointer_field.c";
int32 first(struct Outer* object) {
    views object->inner.data;
    views (object->inner).data[0];
    ensures result == (object->inner).data[0];
}
```

```expect
pass
```
