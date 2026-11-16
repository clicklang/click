# Polynomial expansion is explicit

A product of two sums needs multiple distribution steps. Simple normalization
checks a single written distribution or an already expanded sum of monomials.

```click
theorem needs_distribution(a: Integer, b: Integer) {
    ensures (a + b) * (a - b) == a * a - b * b by { normalize(); }
}
```

```expect
fail: `normalize` goal did not normalize to true
```
