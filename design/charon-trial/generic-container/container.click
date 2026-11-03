import click::integer;
verifying "stack.rs";

// The nodes from `p` on, each owning its allocation, hold `values`, top
// first.
resource nodes<T: Copy>(p: *mut generic_container::Node<T>) {
    field values: List<T>;
    match values {
        List::Nil => { fact p == 0; },
        List::Cons(v, rest) => {
            owns allocation(p, sizeof(generic_container::Node<T>));
            owns *p;
            owns tail: nodes<T>(p.next);
            fact p != 0;
            fact p.value == v;
            fact tail.values == rest;
        },
    }
}

function first<T>(xs: List<T>) -> Option<T> {
    match xs {
        List::Nil => Option<T>::None,
        List::Cons(v, rest) => Option<T>::Some(v),
    }
}

function rest<T>(xs: List<T>) -> List<T> {
    match xs {
        List::Nil => List<T>::Nil,
        List::Cons(v, tail) => tail,
    }
}

function length<T>(xs: List<T>) -> Integer
    decreases xs
{
    match xs {
        List::Nil => 0,
        List::Cons(v, rest) => length(rest) + 1,
    }
}

theorem length_nonnegative<T>(xs: List<T>) {
    ensures length(xs) >= 0 by {
        induct(xs) as ih {
            List::Nil => {
                unfold(length(List<T>::Nil));
                solve();
            }
            List::Cons(value, rest) => {
                apply(ih(rest));
                unfold(length(List<T>::Cons(value, rest)));
                solve() using { length(rest) >= 0; };
            }
        }
    }
}

// The compiler's drop of a node drops its `next` box, which drops that
// node in turn and frees it; the node's value, of the abstract `T`, has no
// drop at the scalar types the stack is used at.
impl<T> Destruct for generic_container::Node<T> {
    fn drop_glue(&mut self) {
        owns self.value;
        owns self.next;
        consumes rest: nodes<T>(self.next);
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

// A stack's drop drops its head.
impl<T> Destruct for generic_container::Stack<T> {
    fn drop_glue(&mut self) {
        owns self.head;
        owns self.len;
        consumes rest: nodes<T>(self.head);
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

// Each method is verified once for every `T`; `len` is the list's length.
impl<T> generic_container::Stack<T> {
    fn new() -> generic_container::Stack<T> {
        produces after: nodes<T>(result.head);
        ensures after.values == List<T>::Nil;
        ensures result.len == 0usize;
        ensures to_integer(result.len) == length(after.values);
    } by {
        step_until(function.exit);
        let after = fold(nodes<T>(result.head), { values: List<T>::Nil }, {});
        unfold(length(List<T>::Nil));
    }

    fn push(&mut self, value: T) {
        owns self.head;
        owns self.len;
        consumes before: nodes<T>(self.head);
        produces after: nodes<T>(self.head);
        requires to_integer(self.len) == length(before.values);
        requires self.len < 18446744073709551615usize;
        ensures after.values == List::Cons(value, old(before.values));
        ensures to_integer(self.len) == length(after.values);
    } by {
        step_until(function.exit);
        let after = fold(nodes<T>(self.head), { values: List::Cons(value, old(before.values)) }, { tail: before });
        unfold(length(List::Cons(value, old(before.values))));
        have to_integer(old(self.len) + 1u64) == to_integer(old(self.len)) + to_integer(1u64);
        solve();
    }

    fn pop(&mut self) -> Option<T> {
        owns self.head;
        owns self.len;
        consumes before: nodes<T>(self.head);
        produces after: nodes<T>(self.head);
        requires to_integer(self.len) == length(before.values);
        ensures result == first(old(before.values));
        ensures after.values == rest(old(before.values));
        ensures to_integer(self.len) == length(after.values);
    } by {
        match before.values {
            List::Nil => {
                let {} = unfold(before);
                step_until(function.exit);
                let after = fold(nodes<T>(self.head), { values: List<T>::Nil }, {});
                unfold(first(List<T>::Nil));
                unfold(rest(List<T>::Nil));
            }
            List::Cons(v, tail_values) => {
                unfold(length(List::Cons(v, tail_values)));
                apply(length_nonnegative(tail_values));
                have to_integer(self.len) >= 1 by solve() using {
                    to_integer(self.len) == length(List::Cons(v, tail_values));
                    length(List::Cons(v, tail_values)) == length(tail_values) + 1;
                    length(tail_values) >= 0;
                };
                unfold(first(List::Cons(v, tail_values)));
                unfold(rest(List::Cons(v, tail_values)));
                let { tail: tail } = unfold(before);
                have separate(memory(self.head), memory(self.len));
                have separate(memory(*self.head), memory(self.head));
                have separate(memory(*self.head), memory(self.len));
                have separate(memory(self.head.next), memory(self.head));
                // Keep the copied next pointer across the imported local writes,
                // then keep the assigned head across the remaining writes and free.
                // Each certificate names one executed operation; skips need no link.
                mark before_pop;
                step_until(function.exit);
                have at(before_pop, separate(region(1).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(1).exit, old(self.head).next) == at(region(1).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(1).footprint, memory(self.head.next))) => at(before_pop, separate(region(1).footprint, memory(self.head.next)));
                        preserve 0 => at(region(1).exit, old(self.head).next) == at(region(1).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(2).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(2).exit, old(self.head).next) == at(region(2).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(2).footprint, memory(self.head.next))) => at(before_pop, separate(region(2).footprint, memory(self.head.next)));
                        preserve 0 => at(region(2).exit, old(self.head).next) == at(region(2).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(3).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(3).exit, old(self.head).next) == at(region(3).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(3).footprint, memory(self.head.next))) => at(before_pop, separate(region(3).footprint, memory(self.head.next)));
                        preserve 0 => at(region(3).exit, old(self.head).next) == at(region(3).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(4).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(4).exit, old(self.head).next) == at(region(4).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(4).footprint, memory(self.head.next))) => at(before_pop, separate(region(4).footprint, memory(self.head.next)));
                        preserve 0 => at(region(4).exit, old(self.head).next) == at(region(4).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(6).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(6).exit, old(self.head).next) == at(region(6).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(6).footprint, memory(self.head.next))) => at(before_pop, separate(region(6).footprint, memory(self.head.next)));
                        preserve 0 => at(region(6).exit, old(self.head).next) == at(region(6).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(9).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(9).exit, old(self.head).next) == at(region(9).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(9).footprint, memory(self.head.next))) => at(before_pop, separate(region(9).footprint, memory(self.head.next)));
                        preserve 0 => at(region(9).exit, old(self.head).next) == at(region(9).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(10).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(10).exit, old(self.head).next) == at(region(10).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(10).footprint, memory(self.head.next))) => at(before_pop, separate(region(10).footprint, memory(self.head.next)));
                        preserve 0 => at(region(10).exit, old(self.head).next) == at(region(10).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(11).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(11).exit, old(self.head).next) == at(region(11).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(11).footprint, memory(self.head.next))) => at(before_pop, separate(region(11).footprint, memory(self.head.next)));
                        preserve 0 => at(region(11).exit, old(self.head).next) == at(region(11).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(12).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(12).exit, old(self.head).next) == at(region(12).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(12).footprint, memory(self.head.next))) => at(before_pop, separate(region(12).footprint, memory(self.head.next)));
                        preserve 0 => at(region(12).exit, old(self.head).next) == at(region(12).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(13).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(13).exit, old(self.head).next) == at(region(13).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(13).footprint, memory(self.head.next))) => at(before_pop, separate(region(13).footprint, memory(self.head.next)));
                        preserve 0 => at(region(13).exit, old(self.head).next) == at(region(13).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(16).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(16).exit, old(self.head).next) == at(region(16).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(16).footprint, memory(self.head.next))) => at(before_pop, separate(region(16).footprint, memory(self.head.next)));
                        preserve 0 => at(region(16).exit, old(self.head).next) == at(region(16).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(17).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(17).exit, old(self.head).next) == at(region(17).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(17).footprint, memory(self.head.next))) => at(before_pop, separate(region(17).footprint, memory(self.head.next)));
                        preserve 0 => at(region(17).exit, old(self.head).next) == at(region(17).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(18).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(18).exit, old(self.head).next) == at(region(18).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(18).footprint, memory(self.head.next))) => at(before_pop, separate(region(18).footprint, memory(self.head.next)));
                        preserve 0 => at(region(18).exit, old(self.head).next) == at(region(18).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(19).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(19).exit, old(self.head).next) == at(region(19).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(19).footprint, memory(self.head.next))) => at(before_pop, separate(region(19).footprint, memory(self.head.next)));
                        preserve 0 => at(region(19).exit, old(self.head).next) == at(region(19).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(25).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(25).exit, old(self.head).next) == at(region(25).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(25).footprint, memory(self.head.next))) => at(before_pop, separate(region(25).footprint, memory(self.head.next)));
                        preserve 0 => at(region(25).exit, old(self.head).next) == at(region(25).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(28).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(28).exit, old(self.head).next) == at(region(28).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(28).footprint, memory(self.head.next))) => at(before_pop, separate(region(28).footprint, memory(self.head.next)));
                        preserve 0 => at(region(28).exit, old(self.head).next) == at(region(28).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(32).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(32).exit, old(self.head).next) == at(region(32).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(32).footprint, memory(self.head.next))) => at(before_pop, separate(region(32).footprint, memory(self.head.next)));
                        preserve 0 => at(region(32).exit, old(self.head).next) == at(region(32).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(38).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(38).exit, old(self.head).next) == at(region(38).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(38).footprint, memory(self.head.next))) => at(before_pop, separate(region(38).footprint, memory(self.head.next)));
                        preserve 0 => at(region(38).exit, old(self.head).next) == at(region(38).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(46).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(46).exit, old(self.head).next) == at(region(46).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(46).footprint, memory(self.head.next))) => at(before_pop, separate(region(46).footprint, memory(self.head.next)));
                        preserve 0 => at(region(46).exit, old(self.head).next) == at(region(46).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(47).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(47).exit, old(self.head).next) == at(region(47).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(47).footprint, memory(self.head.next))) => at(before_pop, separate(region(47).footprint, memory(self.head.next)));
                        preserve 0 => at(region(47).exit, old(self.head).next) == at(region(47).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(49).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(49).exit, old(self.head).next) == at(region(49).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(49).footprint, memory(self.head.next))) => at(before_pop, separate(region(49).footprint, memory(self.head.next)));
                        preserve 0 => at(region(49).exit, old(self.head).next) == at(region(49).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(50).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(50).exit, old(self.head).next) == at(region(50).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(50).footprint, memory(self.head.next))) => at(before_pop, separate(region(50).footprint, memory(self.head.next)));
                        preserve 0 => at(region(50).exit, old(self.head).next) == at(region(50).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(51).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(51).exit, old(self.head).next) == at(region(51).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(51).footprint, memory(self.head.next))) => at(before_pop, separate(region(51).footprint, memory(self.head.next)));
                        preserve 0 => at(region(51).exit, old(self.head).next) == at(region(51).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(59).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(59).exit, old(self.head).next) == at(region(59).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(59).footprint, memory(self.head.next))) => at(before_pop, separate(region(59).footprint, memory(self.head.next)));
                        preserve 0 => at(region(59).exit, old(self.head).next) == at(region(59).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(62).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(62).exit, old(self.head).next) == at(region(62).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(62).footprint, memory(self.head.next))) => at(before_pop, separate(region(62).footprint, memory(self.head.next)));
                        preserve 0 => at(region(62).exit, old(self.head).next) == at(region(62).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(65).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(65).exit, old(self.head).next) == at(region(65).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(65).footprint, memory(self.head.next))) => at(before_pop, separate(region(65).footprint, memory(self.head.next)));
                        preserve 0 => at(region(65).exit, old(self.head).next) == at(region(65).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(72).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(72).exit, old(self.head).next) == at(region(72).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(72).footprint, memory(self.head.next))) => at(before_pop, separate(region(72).footprint, memory(self.head.next)));
                        preserve 0 => at(region(72).exit, old(self.head).next) == at(region(72).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have at(before_pop, separate(region(75).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(75).exit, old(self.head).next) == at(region(75).entry, old(self.head).next) by {
                    transport_certificate {
                        premise 0: at(before_pop, separate(region(75).footprint, memory(self.head.next))) => at(before_pop, separate(region(75).footprint, memory(self.head.next)));
                        preserve 0 => at(region(75).exit, old(self.head).next) == at(region(75).entry, old(self.head).next);
                        conclusion 1;
                    }
                }
                have separate(region(96).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(96).exit, self.head) == at(region(96).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(96).footprint, memory(self.head)) => separate(region(96).footprint, memory(self.head));
                        preserve 0 => at(region(96).exit, self.head) == at(region(96).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(97).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(97).exit, self.head) == at(region(97).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(97).footprint, memory(self.head)) => separate(region(97).footprint, memory(self.head));
                        preserve 0 => at(region(97).exit, self.head) == at(region(97).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(99).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(99).exit, self.head) == at(region(99).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(99).footprint, memory(self.head)) => separate(region(99).footprint, memory(self.head));
                        preserve 0 => at(region(99).exit, self.head) == at(region(99).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(100).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(100).exit, self.head) == at(region(100).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(100).footprint, memory(self.head)) => separate(region(100).footprint, memory(self.head));
                        preserve 0 => at(region(100).exit, self.head) == at(region(100).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(101).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(101).exit, self.head) == at(region(101).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(101).footprint, memory(self.head)) => separate(region(101).footprint, memory(self.head));
                        preserve 0 => at(region(101).exit, self.head) == at(region(101).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(102).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(102).exit, self.head) == at(region(102).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(102).footprint, memory(self.head)) => separate(region(102).footprint, memory(self.head));
                        preserve 0 => at(region(102).exit, self.head) == at(region(102).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(106).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(106).exit, self.head) == at(region(106).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(106).footprint, memory(self.head)) => separate(region(106).footprint, memory(self.head));
                        preserve 0 => at(region(106).exit, self.head) == at(region(106).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(109).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(109).exit, self.head) == at(region(109).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(109).footprint, memory(self.head)) => separate(region(109).footprint, memory(self.head));
                        preserve 0 => at(region(109).exit, self.head) == at(region(109).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(112).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(112).exit, self.head) == at(region(112).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(112).footprint, memory(self.head)) => separate(region(112).footprint, memory(self.head));
                        preserve 0 => at(region(112).exit, self.head) == at(region(112).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(115).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(115).exit, self.head) == at(region(115).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(115).footprint, memory(self.head)) => separate(region(115).footprint, memory(self.head));
                        preserve 0 => at(region(115).exit, self.head) == at(region(115).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(120).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(120).exit, self.head) == at(region(120).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(120).footprint, memory(self.head)) => separate(region(120).footprint, memory(self.head));
                        preserve 0 => at(region(120).exit, self.head) == at(region(120).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(121).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(121).exit, self.head) == at(region(121).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(121).footprint, memory(self.head)) => separate(region(121).footprint, memory(self.head));
                        preserve 0 => at(region(121).exit, self.head) == at(region(121).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(126).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(126).exit, self.head) == at(region(126).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(126).footprint, memory(self.head)) => separate(region(126).footprint, memory(self.head));
                        preserve 0 => at(region(126).exit, self.head) == at(region(126).entry, self.head);
                        conclusion 1;
                    }
                }
                have separate(region(129).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(129).exit, self.head) == at(region(129).entry, self.head) by {
                    transport_certificate {
                        premise 0: separate(region(129).footprint, memory(self.head)) => separate(region(129).footprint, memory(self.head));
                        preserve 0 => at(region(129).exit, self.head) == at(region(129).entry, self.head);
                        conclusion 1;
                    }
                }
                have at(region(91).exit, self.head) == old(self.head.next) by { assumption(); }
                have self.head == old(self.head.next) by { assumption(); }
                have result == Option::Some(v) by {
                    transport(old(self.head.value) == v, result == Option::Some(v)) using {
                        at(before_pop, separate(memory(*self.head), memory(self.head)));
                        at(before_pop, separate(memory(*self.head), memory(self.len)));
                    };
                }
                match tail_values {
                    List::Nil => {
                        let {} = unfold(tail);
                        let after = fold(nodes<T>(self.head), { values: List<T>::Nil }, {});
                        have to_integer(old(self.len) - 1u64) == to_integer(old(self.len)) - to_integer(1u64);
                        unfold(length(List<T>::Nil));
                        have to_integer(old(self.len) - 1u64) == 0 by solve() using {
                            to_integer(old(self.len) - 1u64) == to_integer(old(self.len)) - 1;
                            to_integer(old(self.len)) == length(List::Cons(v, List<T>::Nil));
                            length(List::Cons(v, List<T>::Nil)) == length(List<T>::Nil) + 1;
                            length(List<T>::Nil) == 0;
                        };
                        solve();
                    }
                    List::Cons(w, more) => {
                        let { tail: next } = unfold(tail);
                        have self.head.next == old(self.head.next).next by {
                            rewrite(self.head == old(self.head.next));
                            normalize();
                        }
                        let after = fold(nodes<T>(self.head), { values: List::Cons(w, more) }, { tail: next });
                        have to_integer(old(self.len) - 1u64) == to_integer(old(self.len)) - to_integer(1u64);
                        have to_integer(old(self.len) - 1u64) == length(List::Cons(w, more)) by solve() using {
                            to_integer(old(self.len) - 1u64) == to_integer(old(self.len)) - 1;
                            to_integer(old(self.len)) == length(List::Cons(v, List::Cons(w, more)));
                            length(List::Cons(v, List::Cons(w, more))) == length(List::Cons(w, more)) + 1;
                        };
                        solve();
                    }
                }
            }
        }
    }

    fn size(&self) -> usize {
        views self.head;
        views self.len;
        owns list: nodes<T>(self.head);
        requires to_integer(self.len) == length(list.values);
        ensures to_integer(result) == length(old(list.values));
        ensures list.values == old(list.values);
    }
}

// A value pushed onto a new stack is the one popped, and the stack's drop
// frees what is left.
fn generic_container::round_trip(x: u32) -> Option<u32> {
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

// One layer of `first` and `rest` on a list whose tail is abstract.
theorem first_cons<T>(v: T, xs: List<T>) {
    ensures first(List::Cons(v, xs)) == Option<T>::Some(v) by {
        unfold(first(List::Cons(v, xs)));
        solve();
    }
}

theorem rest_cons<T>(v: T, xs: List<T>) {
    ensures rest(List::Cons(v, xs)) == xs by {
        unfold(rest(List::Cons(v, xs)));
        solve();
    }
}

// Every container holds a list of values, top first, and its size.
trait generic_container::Container<T> {
    function items(self) -> List<T>;
    function size(self) -> usize;
    fn put(&mut self, value: T) {
        requires to_integer(size(self)) == length(items(self));
        requires size(self) < 18446744073709551615usize;
        ensures items(self) == List::Cons(value, old(items(self)));
        ensures to_integer(size(self)) == length(items(self));
    }
    fn take(&mut self) -> Option<T> {
        requires to_integer(size(self)) == length(items(self));
        ensures result == first(old(items(self)));
        ensures items(self) == rest(old(items(self)));
        ensures to_integer(size(self)) == length(items(self));
    }
    fn count(&self) -> usize {
        requires to_integer(size(self)) == length(items(self));
        ensures result == size(self);
    }
}

// The stack is a container for every `T`: its list is the nodes resource
// it holds beside the struct.
impl<T> generic_container::Container<T> for generic_container::Stack<T> {
    resource state: nodes<T>(self.head);
    function items(self) -> List<T> { state.values }
    function size(self) -> usize { self.len }
    fn put(&mut self, value: T) {
    }
    fn take(&mut self) -> Option<T> {
    }
    fn count(&self) -> usize {
    }
}

// Through any container of `u32`: what is put is what is taken, and the
// list is as it was. The proof names the object's state, `items(container)`,
// as the clauses do.
fn generic_container::round_trip_dyn(container: &mut dyn generic_container::Container<u32>, x: u32) -> Option<u32> {
    requires to_integer(size(container)) == length(items(container));
    requires size(container) < 18446744073709551615usize;
    ensures result == Option<u32>::Some(x);
    ensures items(container) == old(items(container));
} by {
    step_until(function.exit);
    apply(first_cons(x, old(items(container))));
    apply(rest_cons(x, old(items(container))));
    solve();
}

// A new stack lent as a container returns what was put.
fn generic_container::through_dyn(x: u32) -> Option<u32> {
    ensures result == Option<u32>::Some(x);
}
