# Open a control whose argument is a loaded pointer

Opening the child control retains the complete pointer-value identity learned
from the parent link. This catches a resource recorder that reconstructs an
incomplete list of facts instead of retaining the operation's constructed facts.
The C function and proof are reduced from the shared-parent nightly fixture.

```c filename=shared_parent.c
struct child {
    int32 refs;
    int32 payload;
};

struct parent {
    struct child* kid;
};

int32 parent_read_payload(struct parent* p) {
    struct child* kid = p->kid;
    return kid->payload;
}

```

```click
spec enum ParentLink {
    Empty,
    Linked(struct child*),
}

resource parent(p: struct parent*) {
    field link: ParentLink;
    match link {
        ParentLink::Empty => {
            owns p->kid;
            fact defined(p->kid);
            fact p->kid == 0;
        },
        ParentLink::Linked(kid) => {
            owns p->kid;
            fact defined(p->kid);
            fact p->kid == kid;
            fact kid != 0;
        },
    }
}

authorized resource child_ref(obj: struct child*) {}

resource child_control(obj: struct child*) {
    owns allocation(obj, sizeof(struct child));
    owns *obj;
    owns authority(child_ref(obj));
    fact defined(obj->refs);
    fact defined(obj->payload);
    fact obj->refs == count(child_ref(obj));
}

verifying "shared_parent.c";

int32 parent_read_payload(struct parent* p) {
    owns link: parent(p);
    requires link.link != ParentLink::Empty;
    owns child_control(p->kid);
    owns child_ref(p->kid);
    ensures result == p->kid->payload;
    ensures result == old(p->kid->payload);
    ensures p->kid == old(p->kid);
    ensures link.link == old(link.link);
    ensures link.link == ParentLink::Linked(old(p->kid));
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(linked_child) => {
            unfold(link);
            have old(p->kid) == linked_child;
            open(child_control(p->kid)) { execute(); }
            let link = fold(parent(p), { link: ParentLink::Linked(linked_child) });
            simp();
        },
    }
}

```
