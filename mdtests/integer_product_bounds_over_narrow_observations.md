# Exact product bounds over narrow observations

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `close() using { ... }`.

```click
theorem unsigned_byte_product(a: uint8, b: uint8) {
    ensures 0 <= to_integer(a) * to_integer(b) by {
        have 0 <= to_integer(a) by { close(); }
        have to_integer(a) <= 255 by { close(); }
        have 0 <= to_integer(b) by { close(); }
        have to_integer(b) <= 255 by { close(); }
        close() using { 0 <= to_integer(a); to_integer(a) <= 255; 0 <= to_integer(b); to_integer(b) <= 255; };
    }
}

theorem short_product_identity(a: int16, b: int16) {
    requires 0 <= to_integer(a) * to_integer(b);
    requires to_integer(a) * to_integer(b) <= 32767;
    let r: int16 = a * b;
    ensures to_integer(r) == to_integer(a) * to_integer(b) by {
        have -32768 <= to_integer(a) by { close(); }
        have to_integer(a) <= 32767 by { close(); }
        have -32768 <= to_integer(b) by { close(); }
        have to_integer(b) <= 32767 by { close(); }
        have to_integer(a) * to_integer(b) <= 1073741824 by {
            close() using { -32768 <= to_integer(a); to_integer(a) <= 32767; -32768 <= to_integer(b); to_integer(b) <= 32767; };
        }
        have to_integer(r) == to_integer(a) * to_integer(b) by {
            close() using { 0 <= to_integer(a) * to_integer(b); to_integer(a) * to_integer(b) <= 32767; };
        }
        close();
    }
}
```

```expect
pass
```
