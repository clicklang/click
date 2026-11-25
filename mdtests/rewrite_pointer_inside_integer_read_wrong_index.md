# An alias equality cannot identify neighboring bytes

Pointer rewriting preserves the byte offset of the selected read. The equality
for the iterator cursor supplies no equality between two input bytes.

```click
theorem wrong_byte(p: const uint8*, bytes: uint8[], n: uint64) {
 requires p == bytes + n;
 ensures to_integer(p[0] as int32) == to_integer((bytes + n)[1] as int32) by {
  rewrite(p, bytes + n);
  close();
 }
}
```

```expect
fail: could not establish `to_integer(((bytes + n)[0] as int32)) == to_integer(((bytes + n)[1] as int32))`
```
