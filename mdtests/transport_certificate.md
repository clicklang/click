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
    have separate(statement(0).footprint, memory(source->data)) by {
        normalize() using { separate(memory(target->pos), memory(source->data)); };
    }
    have source->data == at(before, source->data) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(source->data))
                => separate(statement(0).footprint, memory(source->data));
            preserve 0 => source->data == at(before, source->data);
            conclusion 1;
        }
    }
    step();
    mark final;
    have separate(statement(1).footprint, memory(source->data)) by {
        normalize() using { separate(memory(target->pos), memory(source->data)); };
    }
    have source->data == at(before, source->data) by {
        transport_certificate {
            premise 0: separate(statement(1).footprint, memory(source->data))
                => separate(statement(1).footprint, memory(source->data));
            preserve 0 => source->data == at(after, source->data);
            premise 2: at(after, source->data) == at(before, source->data)
                => at(after, source->data) == at(before, source->data);
            transitive 1, 2 => source->data == at(before, source->data);
            conclusion 3;
        }
    }
    step();
}
```

```expect
pass
```
