# Signed difference through initialized fields

```c filename=span.c
struct span { int32 start; int32 end; };
int32 span_length(struct span* span) { return span->end - span->start; }
```

```click
resource span_bounds(span: struct span*) { owns *span; }
verifying "span.c";
int32 span_length(struct span* span) {
    requires 0 <= span->start;
    requires span->start <= span->end;
    views span_bounds(span);
    ensures to_integer(result) == to_integer(span->end - span->start);
} by {
    with(span_bounds(span)) {
        have defined(span->end - span->start);
        step();
        close();
    }
}
```

```expect
pass
```
