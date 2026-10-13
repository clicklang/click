# A constant local narrowed to `unsigned char` wraps modulo 256

The reproduction of the former bug that refused this conversion as a bare
`type mismatch`. A local initialized from a constant holds that constant,
and converting it to `unsigned char` reduces it modulo 256 as GCC and Clang
do: -56 becomes 200. Initializers, assignments, returns, and arguments
convert alike.

```c filename=a_constant_local_narrowing_wraps_modulo_256.c
int f(void) { int x = -56; unsigned char c = x; return c; }
int g(void) { int x = -56; unsigned char c; c = x; return c; }
unsigned char h(void) { int x = -56; return x; }
int widen(unsigned char b) { return b; }
int k(void) { int x = -56; return widen(x); }
```

```click
verifying "a_constant_local_narrowing_wraps_modulo_256.c";
int32 f() { ensures result == 200 by auto; }
int32 g() { ensures result == 200 by auto; }
uint8 h() { ensures result == 200 by auto; }
int32 widen(uint8 b) { ensures result == b; } by { execute(); simp(); }
int32 k() { ensures result == 200; } by { execute(); simp(); }
```

```expect
pass
```
