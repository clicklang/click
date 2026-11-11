# A contract that cannot be applied names the clause that refused

An external function's contract is applied without a body, so each clause
has to lower on its own. When one does not, the refusal carries that
clause's own error: here `slice::from_raw_parts(p, n)` gives no element
type, and the message says so, not only that the contract "cannot be
applied opaquely".

```c filename=x.c
unsigned long measure(const unsigned char *p, unsigned long n);
unsigned long use(const unsigned char *p, unsigned long n) { return measure(p, n); }
```

```click
import click::rust::slice;
verifying "x.c";
extern unsigned long measure(const unsigned char *p, unsigned long n) {
    ensures result == slice::len(slice::from_raw_parts(p, n));
}
unsigned long use(const unsigned char *p, unsigned long n) {
    ensures result == n;
}
```

```expect
fail: cannot infer type argument T for function `click::rust::slice::from_raw_parts`
```
