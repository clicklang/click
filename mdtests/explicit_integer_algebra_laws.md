# Named algebra laws

```click
import click::integer;
theorem laws(a: Integer, b: Integer, c: Integer) {
    ensures a * (b + c) == a * b + a * c by { apply(integer::multiply_add_left(a,b,c)); }
    ensures a * (b * c) == b * (a * c) by { apply(integer::multiply_swap_front(a,b,c)); }
    ensures -a == -1 * a by { apply(integer::negate_as_product(a)); }
}
theorem coefficients(x: Integer, y: Integer) {
    ensures 3 * (x + y) - 2 * x == x + 3 * y by solve();
    ensures x * 4 + x * -3 == x by solve();
}
theorem polynomial(a: Integer,b:Integer) {
    ensures (a+b)*(a-b) == a*a-b*b by solve();
}
theorem shift(x: Integer,k:Integer) {
    requires 0 <= x;
    requires 0 <= k;
    ensures truncating_quotient(x + 3*k,3) == truncating_quotient(x,3)+k by { close() using { 0 <= x; 0 <= k; }; }
    ensures k + truncating_quotient(x,3) == truncating_quotient(k*3 + x,3) by solve();
}
```

```expect
pass
```
