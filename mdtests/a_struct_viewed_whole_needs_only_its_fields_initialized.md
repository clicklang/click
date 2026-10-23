# A struct viewed whole needs only its fields initialized

`struct pair` has four bytes of padding between `a` and `b`, which no store
ever writes. `first` views the whole object, `*s`. A call needs every byte of
it that holds a value initialized, which the two field stores do; padding
holds nothing to initialize.

```c filename=padded_pair.c
struct pair { int a; long b; };

int first(const struct pair *s) { return s->a; }

int caller(void)
{
	struct pair s;
	s.a = 1;
	s.b = 2;
	return first(&s);
}
```

```click
verifying "padded_pair.c";

int32 first(const struct pair* s) {
    views *s;
    ensures result == s->a;
} by { execute(); simp(); }

int32 caller() {
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
pass
```
