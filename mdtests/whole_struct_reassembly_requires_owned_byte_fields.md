# A viewed byte field cannot complete struct ownership
```c filename=mixed.c
struct mixed { int a; char c; char d; char e; char f; };
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
    owns p->d;
    owns p->e;
    views p->f;
} by { execute(); simp(); }
```
```expect
fail: missing resource fact `owns *p`
```
