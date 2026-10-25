# Explicit callback execution: mutation

```click
resource Buffer(data: int32*) { owns data[0..1]; }
contract void Raw(int32* data) {
 requires data[0] < 100;
 owns data[0..1];
 ensures to_integer(data[0]) == to_integer(old(data[0]) + 1);
}
contract void Buffered(int32* data) {
 requires data[0] < 100;
 owns Buffer(data);
 ensures data[0] > old(data[0]);
}
theorem lift(callback: void (*)(int32*)) executes callback(int32* cell) {
 requires Raw(callback);
 ensures Buffered(callback) by {
 unfold(Buffer(cell)); step(Raw);
 have to_integer(old(cell[0])) < to_integer(old(cell[0]) + 1) by auto();
 have cell[0] > old(cell[0]) by {
     rewrite(to_integer(cell[0]) == to_integer(old(cell[0]) + 1));
     assumption();
 }
 fold(Buffer(cell)); solve();
 }
}
```

```expect
pass
```
