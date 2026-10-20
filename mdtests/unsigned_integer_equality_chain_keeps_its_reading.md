# An unsigned equality chain keeps its Integer observations

The equalities connect machine values to a mathematical Integer. Their
unsigned observations must stay unsigned when arithmetic emits a certificate.

```click
import click::integer;

theorem unsigned_equality_chain(adler: uint64, seed: uint64, value: uint64, specification: Integer) {
    requires to_integer(adler) == to_integer(seed);
    requires to_integer(adler) == to_integer(value);
    requires specification == to_integer(seed);
    ensures to_integer(value) == specification by {
        arithmetic() using {
            to_integer(adler) == to_integer(seed);
            to_integer(adler) == to_integer(value);
            specification == to_integer(seed);
        };
    }
}
```

```expect
pass
```
