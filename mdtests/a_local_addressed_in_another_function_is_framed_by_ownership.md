# one name, one answer about addressability; ownership still frames

`a_returned_pointer_reads_across_stores_to_caller_locals.md` is this program
without `taker`. Adding a function that writes `&guard` — about *its own*
`guard`, in a function `read_literal` never calls — removes `guard` from the
fact-free naming walks.

That is deliberate, and it is the price of the answer being a property of a
*name* rather than of a block. `local:guard` is the same spelling in every
function that declares a `guard`, while the resolution memo and the canonical
projection cache are scoped to a verification and not to a function; a
per-function answer would be computed for whichever function asked first and
served to the next one. A name that any function addresses is therefore
absent for every function on those walks.

The proof still closes through ownership. `read_literal` owns its `guard` and
the three bytes `literal_source` produced, and two owned members of one
composition hold disjoint bytes whatever blocks their pointers are spelled in.
The store `guard = 3` is therefore separate from `message[1]`, and the true
result postcondition verifies.

```c filename=a_local_addressed_in_another_function_is_framed_by_ownership.c
int32* echo(int32* p) { return p; }

uint8* literal_source() {
    return "ok";
}

void taker(void) {
    int32 guard;
    int32* q;
    guard = 0;
    q = echo(&guard);
}

int32 read_literal() {
    uint8* message;
    int32 guard;
    message = literal_source();
    guard = 3;
    return message[1] + guard;
}
```

```click
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "a_local_addressed_in_another_function_is_framed_by_ownership.c";

int32* echo(int32* p) {
    views p[0..1];
    ensures result == p;
} by { execute(); simp(); }

uint8* literal_source() {
    produces result[0..3];
    ensures result[0] == 'o';
    ensures result[1] == 'k';
    ensures result[2] == '\0';
} by {
    execute();
    simp();
}

void taker() {
    ensures 1 == 1;
} by { execute(); simp(); }

int32 read_literal() {
    ensures result == 'k' + 3;
} by {
    execute();
    simp();
}
```

```expect
pass
```
