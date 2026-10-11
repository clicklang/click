# A refused read through a loaded pointer names its element

`s->data[s->len]` reads one element past `views s->data[0..s->len]`. The
refusal names the element as the source writes it, through the loaded
pointer, rather than an unnamed pointer value.

```c filename=a_refused_read_through_a_loaded_pointer_names_its_element.c
struct buf { unsigned char *data; unsigned long len; };
unsigned char last(struct buf *s) { return s->data[s->len]; }
```

```click
verifying "a_refused_read_through_a_loaded_pointer_names_its_element.c";
uint8 last(struct buf* s) {
    views *s;
    views s->data[0..s->len];
} by { execute(); simp(); }
```

```expect
fail: missing resource fact `views s->data[s->len]`
```
