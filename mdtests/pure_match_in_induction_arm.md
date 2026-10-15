# A pure match retains the enclosing induction hypothesis

```click
spec enum Choice { A, B, C }
function copy(xs: List<int32>) -> List<int32>
    decreases xs
{
    match xs { List::Nil => List<int32>::Nil, List::Cons(h, t) => List<int32>::Cons(h, copy(t)), }
}
theorem copy_identity(xs: List<int32>, choice: Choice) {
    ensures copy(xs) == xs by {
        induct(xs) as ih {
            List::Nil => { unfold(copy(List<int32>::Nil)); normalize(); },
            List::Cons(head, tail) => {
                match choice {
                    Choice::C => { apply(ih(tail)); unfold(copy(List<int32>::Cons(head, tail))); simp(); },
                    Choice::A => { apply(ih(tail)); unfold(copy(List<int32>::Cons(head, tail))); simp(); },
                    Choice::B => { apply(ih(tail)); unfold(copy(List<int32>::Cons(head, tail))); simp(); },
                }
            },
        }
    }
}
```
```expect
pass
```
