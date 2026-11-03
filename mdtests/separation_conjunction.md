# Separating conjunction is a descriptor, with explicit library laws

```click
import click::separation;
theorem frame(A: Resource, B: Resource, C: Resource, E: Resource) {
    requires separate(A, C);
    requires separate(B, C);
    requires contains(A * B, E);
    ensures separate(E, C) by {
        apply(separation::separate_star(A, B, C)) using {
            separate(A, C); separate(B, C);
        };
        apply(separation::contains_refl(C)) using {};
        apply(separation::restrict(A * B, C, E, C)) using {
            separate(A * B, C); contains(A * B, E); contains(C, C);
        };
    }
}
theorem components(A: Resource, B: Resource, C: Resource) {
    ensures contains((A * B) * C, B) by {
        apply(separation::contains_left(A * B, C)) using {};
        apply(separation::contains_right(A, B)) using {};
        apply(separation::contains_trans((A * B) * C, A * B, B)) using {
            contains((A * B) * C, A * B); contains(A * B, B);
        };
    }
}
theorem empty(A: Resource) {
    ensures separate(A, separation::emp) by {
        apply(separation::separate_emp(A)) using {};
        apply(separation::separate_symm(separation::emp, A)) using {
            separate(separation::emp, A);
        };
    }
}
```

```expect
pass
```
