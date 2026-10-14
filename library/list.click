spec enum List<T> {
    Nil,
    Cons(T, List<T>),
}

function list_append<T>(xs: List<T>, ys: List<T>) -> List<T>
    decreases xs
{
    match xs {
        List::Nil => ys,
        List::Cons(head, tail) => List<T>::Cons(head, list_append(tail, ys)),
    }
}

function list_contains<T>(xs: List<T>, value: T) -> bool
    decreases xs
{
    match xs {
        List::Nil => false,
        List::Cons(head, tail) =>
            if head == value { true } else { list_contains(tail, value) },
    }
}

theorem list_append_left_identity<T>(xs: List<T>) {
    ensures list_append(List<T>::Nil, xs) == xs by {
        unfold(list_append(List<T>::Nil, xs));
        normalize();
    }
}

theorem list_append_right_identity<T>(xs: List<T>) {
    ensures list_append(xs, List<T>::Nil) == xs by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list_append(List<T>::Nil, List<T>::Nil));
                normalize();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                unfold(list_append(List<T>::Cons(head, tail), List<T>::Nil));
                rewrite(list_append(tail, List<T>::Nil) == tail);
                normalize();
            }
        }
    }
}

theorem list_append_cons<T>(head: T, tail: List<T>, ys: List<T>) {
    ensures list_append(List<T>::Cons(head, tail), ys)
        == List<T>::Cons(head, list_append(tail, ys)) by {
        unfold(list_append(List<T>::Cons(head, tail), ys));
        normalize();
    }
}

theorem list_append_associative<T>(xs: List<T>, ys: List<T>, zs: List<T>) {
    ensures list_append(list_append(xs, ys), zs)
        == list_append(xs, list_append(ys, zs)) by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list_append(List<T>::Nil, ys));
                unfold(list_append(List<T>::Nil, list_append(ys, zs)));
                simp();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                apply(list_append_cons(head, tail, ys));
                rewrite(list_append(List<T>::Cons(head, tail), ys)
                    == List<T>::Cons(head, list_append(tail, ys)));
                apply(list_append_cons(head, list_append(tail, ys), zs));
                rewrite(list_append(List<T>::Cons(head, list_append(tail, ys)), zs)
                    == List<T>::Cons(head, list_append(list_append(tail, ys), zs)));
                apply(list_append_cons(head, tail, list_append(ys, zs)));
                rewrite(list_append(List<T>::Cons(head, tail), list_append(ys, zs))
                    == List<T>::Cons(head, list_append(tail, list_append(ys, zs))));
                rewrite(list_append(list_append(tail, ys), zs)
                    == list_append(tail, list_append(ys, zs)));
                simp();
            }
        }
    }
}

theorem list_contains_nil<T>(value: T) {
    ensures list_contains(List<T>::Nil, value) == false by {
        unfold(list_contains(List<T>::Nil, value));
        normalize();
    }
}

theorem list_contains_cons<T>(head: T, tail: List<T>, value: T) {
    ensures list_contains(List<T>::Cons(head, tail), value)
        == if head == value { true } else { list_contains(tail, value) } by {
        unfold(list_contains(List<T>::Cons(head, tail), value));
        normalize();
    }
}

theorem list_contains_append<T>(xs: List<T>, ys: List<T>, value: T) {
    ensures list_contains(list_append(xs, ys), value)
        == if list_contains(xs, value) { true } else { list_contains(ys, value) } by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list_append(List<T>::Nil, ys));
                unfold(list_contains(List<T>::Nil, value));
                simp();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                apply(list_append_cons(head, tail, ys));
                rewrite(list_append(List<T>::Cons(head, tail), ys)
                    == List<T>::Cons(head, list_append(tail, ys)));
                if head == value {
                    apply(list_contains_cons(head, list_append(tail, ys), value));
                    rewrite(list_contains(List<T>::Cons(head, list_append(tail, ys)), value)
                        == if head == value { true } else { list_contains(list_append(tail, ys), value) });
                    apply(list_contains_cons(head, tail, value));
                    rewrite(list_contains(List<T>::Cons(head, tail), value)
                        == if head == value { true } else { list_contains(tail, value) });
                    normalize() using { head == value; }
                } else {
                    apply(list_contains_cons(head, list_append(tail, ys), value));
                    rewrite(list_contains(List<T>::Cons(head, list_append(tail, ys)), value)
                        == if head == value { true } else { list_contains(list_append(tail, ys), value) });
                    apply(list_contains_cons(head, tail, value));
                    rewrite(list_contains(List<T>::Cons(head, tail), value)
                        == if head == value { true } else { list_contains(tail, value) });
                    rewrite(list_contains(list_append(tail, ys), value)
                        == if list_contains(tail, value) { true } else { list_contains(ys, value) });
                    normalize() using { not(head == value); }
                }
            }
        }
    }
}

function list_length<T>(xs: List<T>) -> Nat
    decreases xs
{
    match xs {
        List::Nil => Nat::Zero,
        List::Cons(head, tail) => Nat::Succ(list_length(tail)),
    }
}

theorem list_length_nil<T>(xs: List<T>) {
    requires xs == List<T>::Nil;
    ensures list_length(xs) == Nat::Zero by {
        rewrite(xs == List<T>::Nil);
        unfold(list_length(List<T>::Nil));
        normalize();
    }
}

theorem list_length_cons<T>(head: T, tail: List<T>) {
    ensures list_length(List<T>::Cons(head, tail)) == Nat::Succ(list_length(tail)) by {
        unfold(list_length(List<T>::Cons(head, tail)));
        normalize();
    }
}

theorem list_length_append<T>(xs: List<T>, ys: List<T>) {
    ensures list_length(list_append(xs, ys)) == nat_add(list_length(xs), list_length(ys)) by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list_append(List<T>::Nil, ys));
                unfold(list_length(List<T>::Nil));
                unfold(nat_add(Nat::Zero, list_length(ys)));
                simp();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                apply(list_append_cons(head, tail, ys));
                rewrite(list_append(List<T>::Cons(head, tail), ys)
                    == List<T>::Cons(head, list_append(tail, ys)));
                apply(list_length_cons(head, list_append(tail, ys)));
                rewrite(list_length(List<T>::Cons(head, list_append(tail, ys)))
                    == Nat::Succ(list_length(list_append(tail, ys))));
                apply(list_length_cons(head, tail));
                rewrite(list_length(List<T>::Cons(head, tail)) == Nat::Succ(list_length(tail)));
                apply(nat_add_succ_left(list_length(tail), list_length(ys)));
                rewrite(nat_add(Nat::Succ(list_length(tail)), list_length(ys))
                    == Nat::Succ(nat_add(list_length(tail), list_length(ys))));
                rewrite(list_length(list_append(tail, ys)) == nat_add(list_length(tail), list_length(ys)));
                normalize();
            }
        }
    }
}
