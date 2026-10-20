verifying "list.rs";

// The nodes from `p` on, each owning its allocation, hold `values`.
resource nodes(p: *mut recursive_drop::Node) {
    field values: List<u32>;
    match values {
        List::Nil => { fact p == 0; },
        List::Cons(v, rest) => {
            owns allocation(p, sizeof(recursive_drop::Node));
            owns *p;
            owns tail: nodes(p.next);
            fact p != 0;
            fact p.value == v;
            fact tail.values == rest;
        },
    }
}

// The compiler's drop of a node drops its `next` box, which drops that
// node in turn and frees it: every node after this one is freed.
impl Destruct for recursive_drop::Node {
    fn drop_glue(&mut self) {
        owns self.value;
        owns self.next;
        consumes rest: nodes(self.next);
        decreases rest;
    } by {
        match rest.values {
            List::Nil => {
                let {} = unfold(rest);
                execute();
            }
            List::Cons(v, tail_values) => {
                let { tail: tail } = unfold(rest);
                execute();
            }
        }
    }
}

impl recursive_drop::Stack {
    // The returned stack's resource is over the struct the caller receives.
    fn new() -> recursive_drop::Stack {
        produces after: nodes(result.head);
        ensures after.values == List<u32>::Nil;
    } by {
        execute();
        let after = fold(nodes(result.head), { values: List<u32>::Nil }, {});
    }

    fn push(&mut self, value: u32) {
        owns self.head;
        consumes before: nodes(self.head);
        produces after: nodes(self.head);
        ensures after.values == List::Cons(value, old(before.values));
    } by {
        execute();
        let after = fold(nodes(self.head), { values: List::Cons(value, old(before.values)) }, { tail: before });
    }

    // Assigning `None` drops every node.
    fn clear(&mut self) {
        owns self.head;
        consumes before: nodes(self.head);
        ensures self.head == 0;
    } by {
        match before.values {
            List::Nil => {
                let {} = unfold(before);
                execute();
            }
            List::Cons(v, rest) => {
                let { tail: tail } = unfold(before);
                execute();
            }
        }
    }
}

// A stack's drop drops its head.
impl Destruct for recursive_drop::Stack {
    fn drop_glue(&mut self) {
        owns self.head;
        consumes rest: nodes(self.head);
    } by {
        match rest.values {
            List::Nil => {
                let {} = unfold(rest);
                execute();
            }
            List::Cons(v, tail_values) => {
                let { tail: tail } = unfold(rest);
                execute();
            }
        }
    }
}

// The stack local is dropped at scope end, which hands the nodes `push`
// produced to its drop glue.
fn recursive_drop::pushed(x: u32) -> u32 {
    ensures result == x;
} by {
    execute();
}
