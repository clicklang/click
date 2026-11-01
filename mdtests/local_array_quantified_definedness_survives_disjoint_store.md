# Quantified definedness of a local array survives a disjoint store

```c filename=local.c
int d(int j)
{
	char tmp[4];
	int unit;
	tmp[0] = 'a';
	tmp[1] = 0;
	unit = j;
	return unit;
}
```

```click
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "local.c";
int32 d(int32 j) {
    ensures true;
} by {
    step();
    step();
    step();
    step();
    have forall (k: uint64) { 0u64 <= k and k < 1u64 implies tmp[k] != 0u8 } by { enumerate(); }
    have forall (k: uint64) { 0u64 <= k and k < 2u64 implies defined(tmp[k]) } by { enumerate(); }
    step();
    have forall (k: uint64) { 0u64 <= k and k < 1u64 implies tmp[k] != 0u8 } by { assumption(); }
    have forall (k: uint64) { 0u64 <= k and k < 2u64 implies defined(tmp[k]) } by { assumption(); }
}
```

```expect
pass
```
