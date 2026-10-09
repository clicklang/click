# Field viewability uses the complete ABI layout

```c filename=widths.c
struct byte { int prefix; unsigned char value; };
void probe_byte(struct byte *p) {}
struct short { int prefix; unsigned short value; };
void probe_short(struct short *p) {}
struct word { int prefix; unsigned int value; };
void probe_word(struct word *p) {}
struct wide { int prefix; unsigned long value; };
void probe_wide(struct wide *p) {}
struct real { int prefix; double value; };
void probe_real(struct real *p) {}
```

```click
verifying "widths.c";
void probe_byte(struct byte *p) {
    views p->value;
    ensures viewable(p->value);
} by { execute(); simp(); }
void probe_short(struct short *p) {
    views p->value;
    ensures viewable(p->value);
} by { execute(); simp(); }
void probe_word(struct word *p) {
    views p->value;
    ensures viewable(p->value);
} by { execute(); simp(); }
void probe_wide(struct wide *p) {
    views p->value;
    ensures viewable(p->value);
} by { execute(); simp(); }
void probe_real(struct real *p) {
    views p->value;
    ensures viewable(p->value);
} by { execute(); simp(); }
```

```expect
pass
```
