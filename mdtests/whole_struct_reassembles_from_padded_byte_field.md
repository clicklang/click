# A padded byte-field slot reassembles with the preceding field

Keep the original reported C and contract. Scalar field ownership includes the
ABI slot up to the next field or the end of the struct, so the byte field
contributes the three tail-padding bytes as well.

```c filename=mixed.c
struct mixed { int a; char c; };
int set_c(struct mixed *p) { p->c = 1; return 0; }
int mixed_fields(struct mixed *p) { set_c(p); return p->a; }
```
```click
verifying "mixed.c";
int32 set_c(struct mixed* p) { owns *p; ensures result == 0; } by { execute(); simp(); }
int32 mixed_fields(struct mixed* p) {
    requires aligned(p, 4);
    owns p->a;
    owns p->c;
} by { execute(); simp(); }
```
```expect
pass
```
