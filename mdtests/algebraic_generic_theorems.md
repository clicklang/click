# generic theorems are checked parametrically and at concrete applications

Generic theorem parameters use the same Rust-like syntax and call-site type
inference as logical functions. Declarations verify with rigid arbitrary types,
without needing callers. Each concrete instance is also checked before an
`apply` step may use its conclusion. This example exercises structural
induction and two distinct element types.

```click
spec enum TestList<T> {
    Nil,
    Cons(T, TestList<T>),
}

spec enum Maybe<T> {
    None,
    Some(T),
}

function append<T>(xs: TestList<T>, ys: TestList<T>) -> TestList<T>
    decreases xs
{
    match xs {
        TestList::Nil => ys,
        TestList::Cons(head, tail) => TestList<T>::Cons(head, append(tail, ys)),
    }
}

theorem append_right_identity<T>(xs: TestList<T>) {
    ensures append(xs, TestList<T>::Nil) == xs by {
        let ih = induct(xs);
        match xs {
            TestList::Nil => {
                unfold(append(TestList<T>::Nil, TestList<T>::Nil));
                close();
            }
            TestList::Cons(head, tail) => {
                apply(ih(tail));
                unfold(append(TestList<T>::Cons(head, tail), TestList<T>::Nil));
                rewrite(append(tail, TestList<T>::Nil), tail);
                close();
            }
        }
    }
}

theorem reflexive<T>(value: T) {
    ensures value == value by close();
}

theorem reflexive_via_generic<T>(value: T) {
    ensures value == value by {
        apply(reflexive(value));
        close();
    }
}

theorem retain<T>(left: T, right: T) {
    requires left == right;
    ensures left == right by {
        close();
    }
}

theorem int32_instance(xs: TestList<int32>) {
    ensures append(xs, TestList<int32>::Nil) == xs by {
        apply(append_right_identity(xs));
        close();
    }
}

theorem pointer_instance(xs: TestList<int32*>) {
    ensures append(xs, TestList<int32*>::Nil) == xs by {
        apply(append_right_identity(xs));
        close();
    }
}

theorem scalar_parameter_instance(value: int32) {
    requires value == value;
    ensures value == value by {
        apply(retain(value, value));
        apply(reflexive_via_generic(value));
        close();
    }
}

theorem generic_requirement_instance(left: int32, right: int32) {
    requires left == right;
    ensures left == right by {
        apply(retain(left, right));
        close();
    }
}

theorem pointer_parameter_instance(value: int32*) {
    ensures value == value by {
        apply(reflexive_via_generic(value));
        close();
    }
}

theorem algebraic_parameter_instance(value: Maybe<int32>) {
    ensures value == value by {
        apply(reflexive_via_generic(value));
        close();
    }
}
```

```expect
pass
```
