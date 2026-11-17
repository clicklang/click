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
                have at(before_pop, separate(region(6).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(6).exit, old(self.head).next) == at(region(6).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(6));
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
                have at(before_pop, separate(region(14).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(14).exit, old(self.head).next) == at(region(14).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(14));
                }
                have at(before_pop, separate(region(15).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(15).exit, old(self.head).next) == at(region(15).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(15));
                }
                have at(before_pop, separate(region(20).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(20).exit, old(self.head).next) == at(region(20).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(20));
                }
                have at(before_pop, separate(region(22).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(22).exit, old(self.head).next) == at(region(22).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(22));
                }
                have at(before_pop, separate(region(25).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(25).exit, old(self.head).next) == at(region(25).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(25));
                }
                have at(before_pop, separate(region(30).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(30).exit, old(self.head).next) == at(region(30).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(30));
                }
                have at(before_pop, separate(region(36).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(36).exit, old(self.head).next) == at(region(36).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(36));
                }
                have at(before_pop, separate(region(37).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(37).exit, old(self.head).next) == at(region(37).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(37));
                }
                have at(before_pop, separate(region(39).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(39).exit, old(self.head).next) == at(region(39).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(39));
                }
                have at(before_pop, separate(region(40).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(40).exit, old(self.head).next) == at(region(40).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(40));
                }
                have at(before_pop, separate(region(41).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(41).exit, old(self.head).next) == at(region(41).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(41));
                }
                have at(before_pop, separate(region(48).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(48).exit, old(self.head).next) == at(region(48).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(48));
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
                have at(before_pop, separate(region(56).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(56).exit, old(self.head).next) == at(region(56).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(56));
                }
                have at(before_pop, separate(region(58).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(58).exit, old(self.head).next) == at(region(58).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(58));
                }
                have at(before_pop, separate(region(60).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(60).exit, old(self.head).next) == at(region(60).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(60));
                }
                have separate(region(74).footprint, memory(self.head)) by { normalize() using {
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(74).exit, self.head) == at(region(74).entry, self.head) by {
                    preserve(memory(self.head), region(74));
                }
                have separate(region(75).footprint, memory(self.head)) by { normalize() using {
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(75).exit, self.head) == at(region(75).entry, self.head) by {
                    preserve(memory(self.head), region(75));
                }
                have at(region(69).exit, self.head) == old(self.head.next) by { known(); }
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
                        have old(self.head.next).next == at(region(75).exit, old(self.head.next).next) by {
                            transport(at(region(75).exit, old(self.head.next).next) == at(region(75).exit, old(self.head.next).next), old(self.head.next).next == at(region(75).exit, old(self.head.next).next));
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
