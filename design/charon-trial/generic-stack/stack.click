import click::integer;
verifying "stack.rs";

// The nodes from `p` on, each owning its allocation, hold `values`, top
// first.
resource nodes<T: Copy>(p: *mut generic_stack::Node<T>) {
    field values: List<T>;
    match values {
        List::Nil => { fact p == 0; },
        List::Cons(v, rest) => {
            owns allocation(p, sizeof(generic_stack::Node<T>));
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
        let ih = induct(xs);
        match xs {
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
impl<T> Destruct for generic_stack::Node<T> {
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
impl<T> Destruct for generic_stack::Stack<T> {
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
impl<T> generic_stack::Stack<T> {
    fn new() -> generic_stack::Stack<T> {
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
                have at(before_pop, separate(region(63).footprint, memory(self.head.next))) by { normalize() using {
                    at(before_pop, separate(memory(self.head.next), memory(self.head)));
                }; }
                have at(region(63).exit, old(self.head).next) == at(region(63).entry, old(self.head).next) by {
                    preserve(at(before_pop, memory(self.head.next)), region(63));
                }
                have separate(region(67).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(67).exit, self.head) == at(region(67).entry, self.head) by {
                    preserve(memory(self.head), region(67));
                }
                have separate(region(72).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(72).exit, self.head) == at(region(72).entry, self.head) by {
                    preserve(memory(self.head), region(72));
                }
                have separate(region(76).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(76).exit, self.head) == at(region(76).entry, self.head) by {
                    preserve(memory(self.head), region(76));
                }
                have separate(region(77).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(77).exit, self.head) == at(region(77).entry, self.head) by {
                    preserve(memory(self.head), region(77));
                }
                have separate(region(83).footprint, memory(self.head)) by { normalize() using {
                    separate(memory(self.head), memory(self.len));
                    at(before_pop, separate(memory(*self.head), memory(self.head)));
                }; }
                have at(region(83).exit, self.head) == at(region(83).entry, self.head) by {
                    preserve(memory(self.head), region(83));
                }
                have at(region(66).exit, self.head) == old(self.head.next) by { known(); }
                have self.head == old(self.head.next) by { known(); }
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
                        have old(self.head.next).next == at(region(77).exit, old(self.head.next).next) by {
                            transport(at(region(77).exit, old(self.head.next).next) == at(region(77).exit, old(self.head.next).next), old(self.head.next).next == at(region(77).exit, old(self.head.next).next));
                        }
                        have self.head.next == old(self.head.next).next by {
                            rewrite(self.head, old(self.head.next));
                            known();
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
fn generic_stack::round_trip(x: u32) -> Option<u32> {
    ensures result == Option<u32>::Some(x);
} by {
    step_until(statement(0).call(0));
    let { after: empty } = step(__rust_q_I13_generic_stack_T42___rust_q_I13_generic_stack_I5_Stack_A3_u32_I3_new, {});
    step_until(statement(1).call(0));
    let { after: pushed } = step(__rust_q_I13_generic_stack_T42___rust_q_I13_generic_stack_I5_Stack_A3_u32_I4_push, { before: empty });
    step_until(statement(2).call(0));
    let { after: remaining } = step(__rust_q_I13_generic_stack_T42___rust_q_I13_generic_stack_I5_Stack_A3_u32_I3_pop, { before: pushed });
    step_until(function.exit);
    unfold(first(List::Cons(x, List<u32>::Nil)));
}
