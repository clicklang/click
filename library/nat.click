spec enum Nat {
    Zero,
    Succ(Nat),
}

theorem nat_integer_zero() {
    ensures to_integer(Nat::Zero) == 0;
}

theorem nat_integer_succ(n: Nat) {
    ensures to_integer(Nat::Succ(n)) == to_integer(n) + 1;
}

theorem nat_integer_nonnegative(n: Nat) {
    ensures to_integer(n) >= 0;
}

theorem nat_integer_round_trip(n: Nat) {
    ensures to_nat(to_integer(n)) == n;
}

theorem integer_nat_round_trip(z: Integer) {
    requires z >= 0;
    ensures to_integer(to_nat(z)) == z;
}

theorem integer_to_nat_zero() {
    ensures to_nat(0) == Nat::Zero;
}


function nat_add(left: Nat, right: Nat) -> Nat
    decreases left
{
    match left {
        Nat::Zero => right,
        Nat::Succ(previous) => Nat::Succ(nat_add(previous, right)),
    }
}

theorem nat_add_left_identity(n: Nat) {
    ensures nat_add(Nat::Zero, n) == n by {
        unfold(nat_add(Nat::Zero, n));
        normalize();
    }
}

theorem nat_add_succ_left(n: Nat, m: Nat) {
    ensures nat_add(Nat::Succ(n), m) == Nat::Succ(nat_add(n, m)) by {
        unfold(nat_add(Nat::Succ(n), m));
        normalize();
    }
}

theorem nat_integer_add(n: Nat, m: Nat) {
    ensures to_integer(nat_add(n, m)) == to_integer(n) + to_integer(m) by {
        induct(n) as ih {
            Nat::Zero => {
                unfold(nat_add(Nat::Zero, m));
                apply(nat_integer_zero());
                arithmetic_certificate {
                    premise 0: to_integer(Nat::Zero) == 0 => to_integer(Nat::Zero) == 0;
                    scale 0 by -1 => to_integer(m) == to_integer(Nat::Zero) + to_integer(m);
                    conclusion 1;
                }
            }
            Nat::Succ(previous) => {
                unfold(nat_add(Nat::Succ(previous), m));
                apply(nat_integer_succ(nat_add(previous, m)));
                apply(ih(previous));
                apply(nat_integer_succ(previous));
                arithmetic_certificate {
                    premise 0: to_integer(Nat::Succ(nat_add(previous, m))) == to_integer(nat_add(previous, m)) + 1 => to_integer(Nat::Succ(nat_add(previous, m))) == to_integer(nat_add(previous, m)) + 1;
                    premise 1: to_integer(nat_add(previous, m)) == to_integer(previous) + to_integer(m) => to_integer(nat_add(previous, m)) == to_integer(previous) + to_integer(m);
                    premise 2: to_integer(Nat::Succ(previous)) == to_integer(previous) + 1 => to_integer(Nat::Succ(previous)) == to_integer(previous) + 1;
                    add 0, 1 => to_integer(Nat::Succ(nat_add(previous, m))) == to_integer(previous) + to_integer(m) + 1;
                    scale 2 by -1 => to_integer(previous) + 1 == to_integer(Nat::Succ(previous));
                    add 3, 4 => to_integer(Nat::Succ(nat_add(previous, m))) == to_integer(Nat::Succ(previous)) + to_integer(m);
                    conclusion 5;
                }
            }
        }
    }
}

theorem nat_add_right_identity(n: Nat) {
    ensures nat_add(n, Nat::Zero) == n by {
        induct(n) as ih {
            Nat::Zero => {
                unfold(nat_add(Nat::Zero, Nat::Zero));
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                unfold(nat_add(Nat::Succ(previous), Nat::Zero));
                rewrite(nat_add(previous, Nat::Zero) == previous);
                normalize();
            }
        }
    }
}

theorem nat_add_succ_right(n: Nat, m: Nat) {
    ensures nat_add(n, Nat::Succ(m)) == Nat::Succ(nat_add(n, m)) by {
        induct(n) as ih {
            Nat::Zero => {
                unfold(nat_add(Nat::Zero, Nat::Succ(m)));
                unfold(nat_add(Nat::Zero, m));
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                unfold(nat_add(Nat::Succ(previous), Nat::Succ(m)));
                unfold(nat_add(Nat::Succ(previous), m));
                rewrite(nat_add(previous, Nat::Succ(m)) == Nat::Succ(nat_add(previous, m)));
                normalize();
            }
        }
    }
}

theorem nat_add_associative(a: Nat, b: Nat, c: Nat) {
    ensures nat_add(nat_add(a, b), c) == nat_add(a, nat_add(b, c)) by {
        induct(a) as ih {
            Nat::Zero => {
                unfold(nat_add(Nat::Zero, b));
                unfold(nat_add(Nat::Zero, nat_add(b, c)));
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                apply(nat_add_succ_left(previous, b));
                rewrite(nat_add(Nat::Succ(previous), b) == Nat::Succ(nat_add(previous, b)));
                apply(nat_add_succ_left(nat_add(previous, b), c));
                rewrite(nat_add(Nat::Succ(nat_add(previous, b)), c)
                    == Nat::Succ(nat_add(nat_add(previous, b), c)));
                apply(nat_add_succ_left(previous, nat_add(b, c)));
                rewrite(nat_add(Nat::Succ(previous), nat_add(b, c))
                    == Nat::Succ(nat_add(previous, nat_add(b, c))));
                rewrite(nat_add(nat_add(previous, b), c) == nat_add(previous, nat_add(b, c)));
                normalize();
            }
        }
    }
}

theorem nat_add_commutative(a: Nat, b: Nat) {
    ensures nat_add(a, b) == nat_add(b, a) by {
        induct(a) as ih {
            Nat::Zero => {
                unfold(nat_add(Nat::Zero, b));
                apply(nat_add_right_identity(b));
                rewrite(nat_add(b, Nat::Zero) == b);
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                unfold(nat_add(Nat::Succ(previous), b));
                apply(nat_add_succ_right(b, previous));
                rewrite(nat_add(b, Nat::Succ(previous)) == Nat::Succ(nat_add(b, previous)));
                rewrite(nat_add(previous, b) == nat_add(b, previous));
                normalize();
            }
        }
    }
}
