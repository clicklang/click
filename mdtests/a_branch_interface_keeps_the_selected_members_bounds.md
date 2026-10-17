# A branch interface keeps the selected member's bounds

Both arms establish the view and bounds for their selected pointer. The
abstract successor retains that evidence for its member read.

```c filename=branch.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* left, struct Pair* right, int32 choose) {
 struct Pair* selected;
 if (choose) { selected = left; } else { selected = right; }
 return selected->second;
}
```
```click
verifying "branch.c";
int32 probe(struct Pair* left, struct Pair* right, int32 choose) {
 views left->second;
 views right->second;
 ensures result == left->second or result == right->second by {
 step();
 branch ensuring {
  fact selected == left or selected == right;
  views selected->second;
 } then { step(); have selected == left or selected == right by { have selected == left by normalize(); assumption(); } }
 else { step(); have selected == left or selected == right by { have selected == right by normalize(); assumption(); } }
 step(); simp();
 }
}
```

```expect
pass
```
