import click::nat;

spec enum List<T> {
    Nil,
    Cons(T, List<T>),
}

function append<T>(xs: List<T>, ys: List<T>) -> List<T>
    decreases xs
{
    match xs {
        List::Nil => ys,
        List::Cons(head, tail) => List<T>::Cons(head, list::append(tail, ys)),
    }
}

function contains<T>(xs: List<T>, value: T) -> bool
    decreases xs
{
    match xs {
        List::Nil => false,
        List::Cons(head, tail) =>
            if head == value { true } else { list::contains(tail, value) },
    }
}

theorem append_left_identity<T>(xs: List<T>) {
    ensures list::append(List<T>::Nil, xs) == xs by {
        unfold(list::append(List<T>::Nil, xs));
        normalize();
    }
}

theorem append_right_identity<T>(xs: List<T>) {
    ensures list::append(xs, List<T>::Nil) == xs by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list::append(List<T>::Nil, List<T>::Nil));
                normalize();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                unfold(list::append(List<T>::Cons(head, tail), List<T>::Nil));
                rewrite(list::append(tail, List<T>::Nil) == tail);
                normalize();
            }
        }
    }
}

theorem append_cons<T>(head: T, tail: List<T>, ys: List<T>) {
    ensures list::append(List<T>::Cons(head, tail), ys)
        == List<T>::Cons(head, list::append(tail, ys)) by {
        unfold(list::append(List<T>::Cons(head, tail), ys));
        normalize();
    }
}

theorem append_associative<T>(xs: List<T>, ys: List<T>, zs: List<T>) {
    ensures list::append(list::append(xs, ys), zs)
        == list::append(xs, list::append(ys, zs)) by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list::append(List<T>::Nil, ys));
                unfold(list::append(List<T>::Nil, list::append(ys, zs)));
                simp();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                apply(list::append_cons(head, tail, ys));
                rewrite(list::append(List<T>::Cons(head, tail), ys)
                    == List<T>::Cons(head, list::append(tail, ys)));
                apply(list::append_cons(head, list::append(tail, ys), zs));
                rewrite(list::append(List<T>::Cons(head, list::append(tail, ys)), zs)
                    == List<T>::Cons(head, list::append(list::append(tail, ys), zs)));
                apply(list::append_cons(head, tail, list::append(ys, zs)));
                rewrite(list::append(List<T>::Cons(head, tail), list::append(ys, zs))
                    == List<T>::Cons(head, list::append(tail, list::append(ys, zs))));
                rewrite(list::append(list::append(tail, ys), zs)
                    == list::append(tail, list::append(ys, zs)));
                simp();
            }
        }
    }
}

theorem contains_nil<T>(value: T) {
    ensures list::contains(List<T>::Nil, value) == false by {
        unfold(list::contains(List<T>::Nil, value));
        normalize();
    }
}

theorem contains_cons<T>(head: T, tail: List<T>, value: T) {
    ensures list::contains(List<T>::Cons(head, tail), value)
        == if head == value { true } else { list::contains(tail, value) } by {
        unfold(list::contains(List<T>::Cons(head, tail), value));
        normalize();
    }
}

theorem contains_append<T>(xs: List<T>, ys: List<T>, value: T) {
    ensures list::contains(list::append(xs, ys), value)
        == if list::contains(xs, value) { true } else { list::contains(ys, value) } by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list::append(List<T>::Nil, ys));
                unfold(list::contains(List<T>::Nil, value));
                simp();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                apply(list::append_cons(head, tail, ys));
                rewrite(list::append(List<T>::Cons(head, tail), ys)
                    == List<T>::Cons(head, list::append(tail, ys)));
                if head == value {
                    apply(list::contains_cons(head, list::append(tail, ys), value));
                    rewrite(list::contains(List<T>::Cons(head, list::append(tail, ys)), value)
                        == if head == value { true } else { list::contains(list::append(tail, ys), value) });
                    apply(list::contains_cons(head, tail, value));
                    rewrite(list::contains(List<T>::Cons(head, tail), value)
                        == if head == value { true } else { list::contains(tail, value) });
                    normalize() using { head == value; }
                } else {
                    apply(list::contains_cons(head, list::append(tail, ys), value));
                    rewrite(list::contains(List<T>::Cons(head, list::append(tail, ys)), value)
                        == if head == value { true } else { list::contains(list::append(tail, ys), value) });
                    apply(list::contains_cons(head, tail, value));
                    rewrite(list::contains(List<T>::Cons(head, tail), value)
                        == if head == value { true } else { list::contains(tail, value) });
                    rewrite(list::contains(list::append(tail, ys), value)
                        == if list::contains(tail, value) { true } else { list::contains(ys, value) });
                    normalize() using { not(head == value); }
                }
            }
        }
    }
}

function length<T>(xs: List<T>) -> Nat
    decreases xs
{
    match xs {
        List::Nil => Nat::Zero,
        List::Cons(head, tail) => Nat::Succ(list::length(tail)),
    }
}

theorem length_nil<T>(xs: List<T>) {
    requires xs == List<T>::Nil;
    ensures list::length(xs) == Nat::Zero by {
        rewrite(xs == List<T>::Nil);
        unfold(list::length(List<T>::Nil));
        normalize();
    }
}

theorem length_cons<T>(head: T, tail: List<T>) {
    ensures list::length(List<T>::Cons(head, tail)) == Nat::Succ(list::length(tail)) by {
        unfold(list::length(List<T>::Cons(head, tail)));
        normalize();
    }
}

theorem length_append<T>(xs: List<T>, ys: List<T>) {
    ensures list::length(list::append(xs, ys)) == nat_add(list::length(xs), list::length(ys)) by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list::append(List<T>::Nil, ys));
                unfold(list::length(List<T>::Nil));
                unfold(nat_add(Nat::Zero, list::length(ys)));
                simp();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                apply(list::append_cons(head, tail, ys));
                rewrite(list::append(List<T>::Cons(head, tail), ys)
                    == List<T>::Cons(head, list::append(tail, ys)));
                apply(list::length_cons(head, list::append(tail, ys)));
                rewrite(list::length(List<T>::Cons(head, list::append(tail, ys)))
                    == Nat::Succ(list::length(list::append(tail, ys))));
                apply(list::length_cons(head, tail));
                rewrite(list::length(List<T>::Cons(head, tail)) == Nat::Succ(list::length(tail)));
                apply(nat_add_succ_left(list::length(tail), list::length(ys)));
                rewrite(nat_add(Nat::Succ(list::length(tail)), list::length(ys))
                    == Nat::Succ(nat_add(list::length(tail), list::length(ys))));
                rewrite(list::length(list::append(tail, ys)) == nat_add(list::length(tail), list::length(ys)));
                normalize();
            }
        }
    }
}
