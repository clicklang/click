# A pure predicate compares a model pointer with its C alias

The resource supplies `p == q`, where `q` is a model pointer. Rewriting `q`
to the C pointer `p` must enter the scalar-returning pure function's arguments
before unfolding it. The structural pointer rewrite used to leave the call
unchanged and report no occurrence, without trying its binder-safe pointer
walker. Algebraic-returning calls already accepted this substitution.

```c filename=alias.c
int f(int *p) { return 0; }
```
```click
verifying "alias.c";
spec enum Link { Node(int32*), }
function points_to(link: Link, p: int32*) -> int32 {
    match link { Link::Node(q) => if q == p { 1 } else { 0 }, }
}
resource Cell(p: int32*) {
    field model: Link;
    match model { Link::Node(q) => { owns p[0..1]; fact p == q; }, }
}
int32 f(int32* p) {
    consumes before: Cell(p);
    produces after: Cell(p);
    ensures result == 0;
} by {
    match before.model {
        Link::Node(q) => {
            unfold(before);
            have points_to(Link::Node(q), p) == 1 by {
                rewrite(q == p);
                unfold(points_to(Link::Node(p), p)); normalize();
            }
            execute();
            let after = fold(Cell(p), { model: Link::Node(q) });
            simp();
        },
    }
}
```
```expect
pass
```
