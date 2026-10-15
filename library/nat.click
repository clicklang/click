spec enum Nat {
    Zero,
    Succ(Nat),
}

theorem to_integer_zero() {
    ensures to_integer(Nat::Zero) == 0;
}

theorem to_integer_succ(n: Nat) {
    ensures to_integer(Nat::Succ(n)) == to_integer(n) + 1;
}

theorem to_integer_nonnegative(n: Nat) {
    ensures to_integer(n) >= 0;
}

theorem to_nat_to_integer(n: Nat) {
    ensures to_nat(to_integer(n)) == n;
}

theorem to_integer_to_nat(z: Integer) {
    requires z >= 0;
    ensures to_integer(to_nat(z)) == z;
}

theorem to_nat_zero() {
    ensures to_nat(0) == Nat::Zero;
}


function add(left: Nat, right: Nat) -> Nat
    decreases left
{
    match left {
        Nat::Zero => right,
        Nat::Succ(previous) => Nat::Succ(nat::add(previous, right)),
    }
}

theorem add_left_identity(n: Nat) {
    ensures nat::add(Nat::Zero, n) == n by {
        unfold(nat::add(Nat::Zero, n));
        normalize();
    }
}

theorem add_succ_left(n: Nat, m: Nat) {
    ensures nat::add(Nat::Succ(n), m) == Nat::Succ(nat::add(n, m)) by {
        unfold(nat::add(Nat::Succ(n), m));
        normalize();
    }
}

theorem to_integer_add(n: Nat, m: Nat) {
    ensures to_integer(nat::add(n, m)) == to_integer(n) + to_integer(m) by {
        induct(n) as ih {
            Nat::Zero => {
                unfold(nat::add(Nat::Zero, m));
                apply(nat::to_integer_zero());
                arithmetic_certificate {
                    premise 0: to_integer(Nat::Zero) == 0 => to_integer(Nat::Zero) == 0;
                    scale 0 by -1 => to_integer(m) == to_integer(Nat::Zero) + to_integer(m);
                    conclusion 1;
                }
            }
            Nat::Succ(previous) => {
                unfold(nat::add(Nat::Succ(previous), m));
                apply(nat::to_integer_succ(nat::add(previous, m)));
                apply(ih(previous));
                apply(nat::to_integer_succ(previous));
                arithmetic_certificate {
                    premise 0: to_integer(Nat::Succ(nat::add(previous, m))) == to_integer(nat::add(previous, m)) + 1 => to_integer(Nat::Succ(nat::add(previous, m))) == to_integer(nat::add(previous, m)) + 1;
                    premise 1: to_integer(nat::add(previous, m)) == to_integer(previous) + to_integer(m) => to_integer(nat::add(previous, m)) == to_integer(previous) + to_integer(m);
                    premise 2: to_integer(Nat::Succ(previous)) == to_integer(previous) + 1 => to_integer(Nat::Succ(previous)) == to_integer(previous) + 1;
                    add 0, 1 => to_integer(Nat::Succ(nat::add(previous, m))) == to_integer(previous) + to_integer(m) + 1;
                    scale 2 by -1 => to_integer(previous) + 1 == to_integer(Nat::Succ(previous));
                    add 3, 4 => to_integer(Nat::Succ(nat::add(previous, m))) == to_integer(Nat::Succ(previous)) + to_integer(m);
                    conclusion 5;
                }
            }
        }
    }
}

theorem add_right_identity(n: Nat) {
    ensures nat::add(n, Nat::Zero) == n by {
        induct(n) as ih {
            Nat::Zero => {
                unfold(nat::add(Nat::Zero, Nat::Zero));
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                unfold(nat::add(Nat::Succ(previous), Nat::Zero));
                rewrite(nat::add(previous, Nat::Zero) == previous);
                normalize();
            }
        }
    }
}

theorem add_succ_right(n: Nat, m: Nat) {
    ensures nat::add(n, Nat::Succ(m)) == Nat::Succ(nat::add(n, m)) by {
        induct(n) as ih {
            Nat::Zero => {
                unfold(nat::add(Nat::Zero, Nat::Succ(m)));
                unfold(nat::add(Nat::Zero, m));
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                unfold(nat::add(Nat::Succ(previous), Nat::Succ(m)));
                unfold(nat::add(Nat::Succ(previous), m));
                rewrite(nat::add(previous, Nat::Succ(m)) == Nat::Succ(nat::add(previous, m)));
                normalize();
            }
        }
    }
}

theorem add_associative(a: Nat, b: Nat, c: Nat) {
    ensures nat::add(nat::add(a, b), c) == nat::add(a, nat::add(b, c)) by {
        induct(a) as ih {
            Nat::Zero => {
                unfold(nat::add(Nat::Zero, b));
                unfold(nat::add(Nat::Zero, nat::add(b, c)));
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                apply(nat::add_succ_left(previous, b));
                rewrite(nat::add(Nat::Succ(previous), b) == Nat::Succ(nat::add(previous, b)));
                apply(nat::add_succ_left(nat::add(previous, b), c));
                rewrite(nat::add(Nat::Succ(nat::add(previous, b)), c)
                    == Nat::Succ(nat::add(nat::add(previous, b), c)));
                apply(nat::add_succ_left(previous, nat::add(b, c)));
                rewrite(nat::add(Nat::Succ(previous), nat::add(b, c))
                    == Nat::Succ(nat::add(previous, nat::add(b, c))));
                rewrite(nat::add(nat::add(previous, b), c) == nat::add(previous, nat::add(b, c)));
                normalize();
            }
        }
    }
}

theorem add_commutative(a: Nat, b: Nat) {
    ensures nat::add(a, b) == nat::add(b, a) by {
        induct(a) as ih {
            Nat::Zero => {
                unfold(nat::add(Nat::Zero, b));
                apply(nat::add_right_identity(b));
                rewrite(nat::add(b, Nat::Zero) == b);
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                unfold(nat::add(Nat::Succ(previous), b));
                apply(nat::add_succ_right(b, previous));
                rewrite(nat::add(b, Nat::Succ(previous)) == Nat::Succ(nat::add(b, previous)));
                rewrite(nat::add(previous, b) == nat::add(b, previous));
                normalize();
            }
        }
    }
}
