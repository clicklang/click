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

function first(xs: List<u32>) -> Option<u32> {
    match xs {
        List::Nil => Option<u32>::None,
        List::Cons(v, rest) => Option<u32>::Some(v),
    }
}

function rest(xs: List<u32>) -> List<u32> {
    match xs {
        List::Nil => List<u32>::Nil,
        List::Cons(v, tail) => tail,
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
                step_until(function.exit);
            }
            List::Cons(v, tail_values) => {
                let { tail: tail } = unfold(rest);
                step_until(function.exit);
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
        step_until(function.exit);
        let after = fold(nodes(result.head), { values: List<u32>::Nil }, {});
    }

    fn push(&mut self, value: u32) {
        owns self.head;
        consumes before: nodes(self.head);
        produces after: nodes(self.head);
        ensures after.values == List::Cons(value, old(before.values));
    } by {
        step_until(function.exit);
        let after = fold(nodes(self.head), { values: List::Cons(value, old(before.values)) }, { tail: before });
    }

    // `self.head.take()?` returns `None` from an empty stack; otherwise the
    // head node's `next` becomes the head and the node is freed.
    fn pop(&mut self) -> Option<u32> {
        owns self.head;
        consumes before: nodes(self.head);
        produces after: nodes(self.head);
        ensures result == first(old(before.values));
        ensures after.values == rest(old(before.values));
    } by {
        match before.values {
            List::Nil => {
                let {} = unfold(before);
                step_until(function.exit);
                let after = fold(nodes(self.head), { values: List<u32>::Nil }, {});
                unfold(first(List<u32>::Nil));
                unfold(rest(List<u32>::Nil));
            }
            List::Cons(v, tail_values) => {
                let { tail: tail } = unfold(before);
                have separate(memory(self.head.next), memory(self.head));
                have separate(memory(*self.head), memory(self.head));
                // Keep the copied next pointer across the imported local writes,
                // then keep the assigned head across the remaining writes and free.
                // Each certificate names one executed operation; skips need no link.
                mark before_pop;
                step_until(function.exit);
                have at(before_pop, separate(region(1).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(1).exit, old(self.head).next) == at(region(1).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(1));
                }
                have at(before_pop, separate(region(2).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(2).exit, old(self.head).next) == at(region(2).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(2));
                }
                have at(before_pop, separate(region(3).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(3).exit, old(self.head).next) == at(region(3).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(3));
                }
                have at(before_pop, separate(region(4).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(4).exit, old(self.head).next) == at(region(4).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(4));
                }
                have at(before_pop, separate(region(5).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(5).exit, old(self.head).next) == at(region(5).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(5));
                }
                have at(before_pop, separate(region(7).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(7).exit, old(self.head).next) == at(region(7).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(7));
                }
                have at(before_pop, separate(region(8).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(8).exit, old(self.head).next) == at(region(8).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(8));
                }
                have at(before_pop, separate(region(9).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(9).exit, old(self.head).next) == at(region(9).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(9));
                }
                have at(before_pop, separate(region(10).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(10).exit, old(self.head).next) == at(region(10).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(10));
                }
                have at(before_pop, separate(region(11).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(11).exit, old(self.head).next) == at(region(11).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(11));
                }
                have at(before_pop, separate(region(16).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(16).exit, old(self.head).next) == at(region(16).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(16));
                }
                have at(before_pop, separate(region(18).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(18).exit, old(self.head).next) == at(region(18).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(18));
                }
                have at(before_pop, separate(region(21).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(21).exit, old(self.head).next) == at(region(21).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(21));
                }
                have at(before_pop, separate(region(26).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(26).exit, old(self.head).next) == at(region(26).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(26));
                }
                have at(before_pop, separate(region(35).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(35).exit, old(self.head).next) == at(region(35).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(35));
                }
                have at(before_pop, separate(region(42).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(42).exit, old(self.head).next) == at(region(42).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(42));
                }
                have at(before_pop, separate(region(44).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(44).exit, old(self.head).next) == at(region(44).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(44));
                }
                have at(before_pop, separate(region(46).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(46).exit, old(self.head).next) == at(region(46).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(46));
                }
                have at(before_pop, separate(region(50).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(50).exit, old(self.head).next) == at(region(50).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(50));
                }
                have at(before_pop, separate(region(52).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(52).exit, old(self.head).next) == at(region(52).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(52));
                }
                have at(before_pop, separate(region(54).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(54).exit, old(self.head).next) == at(region(54).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(54));
                }
                have separate(region(68).footprint, memory(self.head)) by { normalize() using {
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(68).exit, self.head) == at(region(68).entry, self.head) by {
                    preserve(memory(self.head), region(68));
                }
                have separate(region(69).footprint, memory(self.head)) by { normalize() using {
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(69).exit, self.head) == at(region(69).entry, self.head) by {
                    preserve(memory(self.head), region(69));
                }
                have at(region(63).exit, self.head) == old(self.head.next) by { known(); }
                have self.head == old(self.head.next) by { known(); }
                unfold(first(List::Cons(v, tail_values)));
                unfold(rest(List::Cons(v, tail_values)));
                match tail_values {
                    List::Nil => {
                        let {} = unfold(tail);
                        let after = fold(nodes(self.head), { values: List<u32>::Nil }, {});
                    }
                    List::Cons(w, more) => {
                        let { tail: next } = unfold(tail);
                        have old(self.head.next).next == at(region(69).exit, old(self.head.next).next) by {
                            transport(at(region(69).exit, old(self.head.next).next) == at(region(69).exit, old(self.head.next).next), old(self.head.next).next == at(region(69).exit, old(self.head.next).next));
                        }
                        have self.head.next == old(self.head.next).next by {
                            rewrite(self.head, old(self.head.next));
                            known();
                        }
                        have self.head.value == w by {
                            rewrite(self.head, old(self.head.next));
                            known();
                        }
                        let after = fold(nodes(self.head), { values: List::Cons(w, more) }, { tail: next });
                    }
                }
            }
        }
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
                step_until(function.exit);
            }
            List::Cons(v, rest) => {
                let { tail: tail } = unfold(before);
                step_until(function.exit);
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
                step_until(function.exit);
            }
            List::Cons(v, tail_values) => {
                let { tail: tail } = unfold(rest);
                step_until(function.exit);
            }
        }
    }
}

// The stack local is dropped at scope end, which hands the nodes `push`
// produced to its drop glue.
fn recursive_drop::pushed(x: u32) -> u32 {
    ensures result == x;
}

// A value pushed onto a new stack is the one popped, and the stack's drop
// frees what is left.
fn recursive_drop::round_trip(x: u32) -> Option<u32> {
    ensures result == Option<u32>::Some(x);
} by {
    step_until(statement(2).call(0));
    step_until(function.exit);
    unfold(first(List::Cons(x, List<u32>::Nil)));
}
