# Exact product bounds over narrow observations

`integer_product_bounds` reads each operand bound by its value (rule W). In
`to_integer(a) * to_integer(b)` at `uint8` and `int16` an operand is read
through C's promotion to `int32`, a term `to_integer(a)` as written in a
premise does not name; the bound still names the operand's value. Before,
the certificate refused these premises at 8 and 16 bits and accepted them
at 32 and 64. The second theorem is the shape `solve` plans for a product's
lower bound and `click expand` writes
(`a_product_of_64_bit_values_is_its_exact_product.md`).

```click
theorem unsigned_byte_product(a: uint8, b: uint8) {
    ensures 0 <= to_integer(a) * to_integer(b) by {
        have 0 <= to_integer(a) by { solve(); }
        have to_integer(a) <= 255 by { solve(); }
        have 0 <= to_integer(b) by { solve(); }
        have to_integer(b) <= 255 by { solve(); }
        arithmetic_certificate rules {
            premise 0: 0 <= to_integer(a) => 0 <= to_integer(a);
            premise 1: to_integer(a) <= 255 => to_integer(a) <= 255;
            premise 2: 0 <= to_integer(b) => 0 <= to_integer(b);
            premise 3: to_integer(b) <= 255 => to_integer(b) <= 255;
            integer_product_bounds bounds [0, 1, 2, 3] => 0 <= to_integer(a) * to_integer(b);
            conclusion 0;
        }
    }
}

theorem short_product_identity(a: int16, b: int16) {
    requires 0 <= to_integer(a) * to_integer(b);
    requires to_integer(a) * to_integer(b) <= 32767;
    let r: int16 = a * b;
    ensures to_integer(r) == to_integer(a) * to_integer(b) by {
        have -32768 <= to_integer(a) by { solve(); }
        have to_integer(a) <= 32767 by { solve(); }
        have -32768 <= to_integer(b) by { solve(); }
        have to_integer(b) <= 32767 by { solve(); }
        have to_integer(a) * to_integer(b) <= 1073741824 by {
            arithmetic_certificate rules {
                premise 0: -32768 <= to_integer(a) => -32768 <= to_integer(a);
                premise 1: to_integer(a) <= 32767 => to_integer(a) <= 32767;
                premise 2: -32768 <= to_integer(b) => -32768 <= to_integer(b);
                premise 3: to_integer(b) <= 32767 => to_integer(b) <= 32767;
                integer_product_bounds bounds [0, 1, 2, 3] => to_integer(a) * to_integer(b) <= 1073741824;
                conclusion 0;
            }
        }
        have to_integer(r) == to_integer(a) * to_integer(b) by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(a) * to_integer(b) => 0 <= to_integer(a) * to_integer(b);
                premise 1: to_integer(a) * to_integer(b) <= 32767 => to_integer(a) * to_integer(b) <= 32767;
                integer_operation_identity bounds [0, 1] => to_integer(r) == to_integer(a) * to_integer(b);
                conclusion 0;
            }
        }
        assumption();
    }
}
```

```expect
pass
```
