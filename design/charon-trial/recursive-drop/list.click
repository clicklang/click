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
                have at(before_pop, separate(region(1).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(1).exit, old(self.head).next) == at(region(1).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(1).footprint, memory(self.head.next))) => at(before_pop, separate(region(1).footprint, memory(self.head.next)));
                        preserve 0 => at(region(1).exit, old(self.head).next) == at(region(1).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(2).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(2).exit, old(self.head).next) == at(region(2).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(2).footprint, memory(self.head.next))) => at(before_pop, separate(region(2).footprint, memory(self.head.next)));
                        preserve 0 => at(region(2).exit, old(self.head).next) == at(region(2).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(3).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(3).exit, old(self.head).next) == at(region(3).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(3).footprint, memory(self.head.next))) => at(before_pop, separate(region(3).footprint, memory(self.head.next)));
                        preserve 0 => at(region(3).exit, old(self.head).next) == at(region(3).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(4).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(4).exit, old(self.head).next) == at(region(4).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(4).footprint, memory(self.head.next))) => at(before_pop, separate(region(4).footprint, memory(self.head.next)));
                        preserve 0 => at(region(4).exit, old(self.head).next) == at(region(4).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(6).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(6).exit, old(self.head).next) == at(region(6).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(6).footprint, memory(self.head.next))) => at(before_pop, separate(region(6).footprint, memory(self.head.next)));
                        preserve 0 => at(region(6).exit, old(self.head).next) == at(region(6).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(9).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(9).exit, old(self.head).next) == at(region(9).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(9).footprint, memory(self.head.next))) => at(before_pop, separate(region(9).footprint, memory(self.head.next)));
                        preserve 0 => at(region(9).exit, old(self.head).next) == at(region(9).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(10).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(10).exit, old(self.head).next) == at(region(10).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(10).footprint, memory(self.head.next))) => at(before_pop, separate(region(10).footprint, memory(self.head.next)));
                        preserve 0 => at(region(10).exit, old(self.head).next) == at(region(10).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(11).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(11).exit, old(self.head).next) == at(region(11).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(11).footprint, memory(self.head.next))) => at(before_pop, separate(region(11).footprint, memory(self.head.next)));
                        preserve 0 => at(region(11).exit, old(self.head).next) == at(region(11).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(12).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(12).exit, old(self.head).next) == at(region(12).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(12).footprint, memory(self.head.next))) => at(before_pop, separate(region(12).footprint, memory(self.head.next)));
                        preserve 0 => at(region(12).exit, old(self.head).next) == at(region(12).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(15).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(15).exit, old(self.head).next) == at(region(15).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(15).footprint, memory(self.head.next))) => at(before_pop, separate(region(15).footprint, memory(self.head.next)));
                        preserve 0 => at(region(15).exit, old(self.head).next) == at(region(15).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(16).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(16).exit, old(self.head).next) == at(region(16).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(16).footprint, memory(self.head.next))) => at(before_pop, separate(region(16).footprint, memory(self.head.next)));
                        preserve 0 => at(region(16).exit, old(self.head).next) == at(region(16).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(17).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(17).exit, old(self.head).next) == at(region(17).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(17).footprint, memory(self.head.next))) => at(before_pop, separate(region(17).footprint, memory(self.head.next)));
                        preserve 0 => at(region(17).exit, old(self.head).next) == at(region(17).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(18).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(18).exit, old(self.head).next) == at(region(18).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(18).footprint, memory(self.head.next))) => at(before_pop, separate(region(18).footprint, memory(self.head.next)));
                        preserve 0 => at(region(18).exit, old(self.head).next) == at(region(18).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(24).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(24).exit, old(self.head).next) == at(region(24).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(24).footprint, memory(self.head.next))) => at(before_pop, separate(region(24).footprint, memory(self.head.next)));
                        preserve 0 => at(region(24).exit, old(self.head).next) == at(region(24).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(27).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(27).exit, old(self.head).next) == at(region(27).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(27).footprint, memory(self.head.next))) => at(before_pop, separate(region(27).footprint, memory(self.head.next)));
                        preserve 0 => at(region(27).exit, old(self.head).next) == at(region(27).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(31).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(31).exit, old(self.head).next) == at(region(31).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(31).footprint, memory(self.head.next))) => at(before_pop, separate(region(31).footprint, memory(self.head.next)));
                        preserve 0 => at(region(31).exit, old(self.head).next) == at(region(31).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(37).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(37).exit, old(self.head).next) == at(region(37).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(37).footprint, memory(self.head.next))) => at(before_pop, separate(region(37).footprint, memory(self.head.next)));
                        preserve 0 => at(region(37).exit, old(self.head).next) == at(region(37).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(45).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(45).exit, old(self.head).next) == at(region(45).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(45).footprint, memory(self.head.next))) => at(before_pop, separate(region(45).footprint, memory(self.head.next)));
                        preserve 0 => at(region(45).exit, old(self.head).next) == at(region(45).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(46).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(46).exit, old(self.head).next) == at(region(46).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(46).footprint, memory(self.head.next))) => at(before_pop, separate(region(46).footprint, memory(self.head.next)));
                        preserve 0 => at(region(46).exit, old(self.head).next) == at(region(46).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(48).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(48).exit, old(self.head).next) == at(region(48).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(48).footprint, memory(self.head.next))) => at(before_pop, separate(region(48).footprint, memory(self.head.next)));
                        preserve 0 => at(region(48).exit, old(self.head).next) == at(region(48).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(49).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(49).exit, old(self.head).next) == at(region(49).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(49).footprint, memory(self.head.next))) => at(before_pop, separate(region(49).footprint, memory(self.head.next)));
                        preserve 0 => at(region(49).exit, old(self.head).next) == at(region(49).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(50).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(50).exit, old(self.head).next) == at(region(50).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(50).footprint, memory(self.head.next))) => at(before_pop, separate(region(50).footprint, memory(self.head.next)));
                        preserve 0 => at(region(50).exit, old(self.head).next) == at(region(50).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(58).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(58).exit, old(self.head).next) == at(region(58).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(58).footprint, memory(self.head.next))) => at(before_pop, separate(region(58).footprint, memory(self.head.next)));
                        preserve 0 => at(region(58).exit, old(self.head).next) == at(region(58).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(61).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(61).exit, old(self.head).next) == at(region(61).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(61).footprint, memory(self.head.next))) => at(before_pop, separate(region(61).footprint, memory(self.head.next)));
                        preserve 0 => at(region(61).exit, old(self.head).next) == at(region(61).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(64).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(64).exit, old(self.head).next) == at(region(64).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(64).footprint, memory(self.head.next))) => at(before_pop, separate(region(64).footprint, memory(self.head.next)));
                        preserve 0 => at(region(64).exit, old(self.head).next) == at(region(64).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(71).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(71).exit, old(self.head).next) == at(region(71).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(71).footprint, memory(self.head.next))) => at(before_pop, separate(region(71).footprint, memory(self.head.next)));
                        preserve 0 => at(region(71).exit, old(self.head).next) == at(region(71).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(74).footprint, memory(self.head.next))) by { normalize() using { at(before_pop, separate(memory(self.head.next), memory(self.head))); }; }
                have at(region(74).exit, old(self.head).next) == at(region(74).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(74).footprint, memory(self.head.next))) => at(before_pop, separate(region(74).footprint, memory(self.head.next)));
                        preserve 0 => at(region(74).exit, old(self.head).next) == at(region(74).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have separate(region(95).footprint, memory(self.head)) by { normalize() using { at(before_pop, separate(memory(*self.head), memory(self.head))); }; }
                have at(region(95).exit, self.head) == at(region(95).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(95).footprint, memory(self.head)) => separate(region(95).footprint, memory(self.head));
                        preserve 0 => at(region(95).exit, self.head) == at(region(95).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(98).footprint, memory(self.head)) by { normalize() using { at(before_pop, separate(memory(*self.head), memory(self.head))); }; }
                have at(region(98).exit, self.head) == at(region(98).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(98).footprint, memory(self.head)) => separate(region(98).footprint, memory(self.head));
                        preserve 0 => at(region(98).exit, self.head) == at(region(98).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(101).footprint, memory(self.head)) by { normalize() using { at(before_pop, separate(memory(*self.head), memory(self.head))); }; }
                have at(region(101).exit, self.head) == at(region(101).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(101).footprint, memory(self.head)) => separate(region(101).footprint, memory(self.head));
                        preserve 0 => at(region(101).exit, self.head) == at(region(101).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(106).footprint, memory(self.head)) by { normalize() using { at(before_pop, separate(memory(*self.head), memory(self.head))); }; }
                have at(region(106).exit, self.head) == at(region(106).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(106).footprint, memory(self.head)) => separate(region(106).footprint, memory(self.head));
                        preserve 0 => at(region(106).exit, self.head) == at(region(106).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(107).footprint, memory(self.head)) by { normalize() using { at(before_pop, separate(memory(*self.head), memory(self.head))); }; }
                have at(region(107).exit, self.head) == at(region(107).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(107).footprint, memory(self.head)) => separate(region(107).footprint, memory(self.head));
                        preserve 0 => at(region(107).exit, self.head) == at(region(107).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(112).footprint, memory(self.head)) by { normalize() using { at(before_pop, separate(memory(*self.head), memory(self.head))); }; }
                have at(region(112).exit, self.head) == at(region(112).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(112).footprint, memory(self.head)) => separate(region(112).footprint, memory(self.head));
                        preserve 0 => at(region(112).exit, self.head) == at(region(112).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(115).footprint, memory(self.head)) by { normalize() using { at(before_pop, separate(memory(*self.head), memory(self.head))); }; }
                have at(region(115).exit, self.head) == at(region(115).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(115).footprint, memory(self.head)) => separate(region(115).footprint, memory(self.head));
                        preserve 0 => at(region(115).exit, self.head) == at(region(115).entry, self.head);
                        conclusion 1;
                    }
                }
                have at(region(90).exit, self.head) == old(self.head.next) by { assumption(); }
                have self.head == old(self.head.next) by { assumption(); }
                unfold(first(List::Cons(v, tail_values)));
                unfold(rest(List::Cons(v, tail_values)));
                match tail_values {
                    List::Nil => {
                        let {} = unfold(tail);
                        let after = fold(nodes(self.head), { values: List<u32>::Nil }, {});
                    }
                    List::Cons(w, more) => {
                        let { tail: next } = unfold(tail);
                        have old(self.head.next).next == at(region(107).exit, old(self.head.next).next) by {
                            transport(at(region(107).exit, old(self.head.next).next) == at(region(107).exit, old(self.head.next).next), old(self.head.next).next == at(region(107).exit, old(self.head.next).next));
                        }
                        have self.head.next == old(self.head.next).next by {
                            rewrite(self.head == old(self.head.next));
                            assumption();
                        }
                        have self.head.value == w by {
                            rewrite(self.head == old(self.head.next));
                            assumption();
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
    step_until(region(57));
    have separate(region(50).footprint, memory(stack.head)) by { normalize() using {}; }
    have at(region(50).exit, stack.head) == at(region(50).entry, stack.head) by {
        transport_certificate {
            premise 0: separate(region(50).footprint, memory(stack.head)) => separate(region(50).footprint, memory(stack.head));
            preserve 0 => at(region(50).exit, stack.head) == at(region(50).entry, stack.head);
            conclusion 1;
        }
    }
    have separate(region(54).footprint, memory(stack.head)) by { normalize() using {}; }
    have at(region(54).exit, stack.head) == at(region(54).entry, stack.head) by {
        transport_certificate {
            premise 0: separate(region(54).footprint, memory(stack.head)) => separate(region(54).footprint, memory(stack.head));
            preserve 0 => at(region(54).exit, stack.head) == at(region(54).entry, stack.head);
            conclusion 1;
        }
    }
    have separate(region(55).footprint, memory(stack.head)) by { normalize() using {}; }
    have at(region(55).exit, stack.head) == at(region(55).entry, stack.head) by {
        transport_certificate {
            premise 0: separate(region(55).footprint, memory(stack.head)) => separate(region(55).footprint, memory(stack.head));
            preserve 0 => at(region(55).exit, stack.head) == at(region(55).entry, stack.head);
            conclusion 1;
        }
    }
    step_until(function.exit);
    unfold(first(List::Cons(x, List<u32>::Nil)));
}
