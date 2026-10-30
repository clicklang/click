# Explicit transport certificate across two stores

```c filename=fields.c
struct cursor { int pos; int len; int *data; };
void copy_pos(struct cursor *target, struct cursor *source) {
    target->pos = source->pos;
    target->pos = source->len;
}
```

```click
import click::separation;
verifying "fields.c";

void copy_pos(struct cursor *target, struct cursor *source) {
    owns *target;
    views *source;
    requires separate(memory(*target), memory(*source));
} by {
    have contains(memory(*target), memory(target->pos)) by { normalize(); }
    have contains(memory(*source), memory(source->data)) by { normalize(); }
    have separate(memory(target->pos), memory(source->data)) by {
        apply(separation::restrict(memory(*target), memory(*source),
            memory(target->pos), memory(source->data))) using {
            separate(memory(*target), memory(*source));
            contains(memory(*target), memory(target->pos));
            contains(memory(*source), memory(source->data));
        };
    }
    mark before;
    step();
    mark after;
    have source->data == at(before, source->data) by {
        transport_certificate {
            premise 0: changes_only(before, after, memory(target->pos))
                => changes_only(before, after, memory(target->pos));
            premise 1: at(before, separate(memory(target->pos), memory(source->data)))
                => at(before, separate(memory(target->pos), memory(source->data)));
            preserve 0, 1 => source->data == at(before, source->data);
            conclusion 2;
        }
    }
    step();
    mark final;
    have source->data == at(before, source->data) by {
        transport_certificate {
            premise 0: changes_only(after, final, memory(target->pos))
                => changes_only(after, final, memory(target->pos));
            premise 1: at(before, separate(memory(target->pos), memory(source->data)))
                => at(before, separate(memory(target->pos), memory(source->data)));
            preserve 0, 1 => source->data == at(after, source->data);
            premise 3: at(after, source->data) == at(before, source->data)
                => at(after, source->data) == at(before, source->data);
            transitive 2, 3 => source->data == at(before, source->data);
            conclusion 4;
        }
    }
    step();
}
```

```expect
pass
```
