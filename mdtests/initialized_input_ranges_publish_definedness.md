# Initialized input ranges expose their typed reads as entry facts

```c filename=initialized_inputs.c
int32 narrow(int32 *p, int32 lo, int32 hi, int32 k) { return 0; }
int32 wide(uint8 *p, uint64 lo, uint64 k, uint64 i) { return 0; }
int32 pointers(int32 **p, int32 n, int32 k) { return 0; }
```

```click
verifying "initialized_inputs.c";
int32 narrow(int32 *p, int32 lo, int32 hi, int32 k) {
    requires 0 <= lo;
    requires lo <= k;
    requires k < hi;
    views p[lo..hi];
    ensures result == 0;
} by {
    have forall (j: int32) { lo <= j and j < hi implies defined(p[j]) } by { known(); }
    have defined(p[k]) by {
        instantiate(forall (j: int32) { lo <= j and j < hi implies defined(p[j]) }, k) using { lo <= k; k < hi; };
        known();
    }
}
int32 wide(uint8 *p, uint64 lo, uint64 k, uint64 i) {
    requires lo <= i;
    requires i < k;
    views p[lo..k];
    ensures result == 0;
} by {
    have forall (j: uint64) { lo <= j and j < k implies defined(p[j]) } by { known(); }
    have defined(p[i]) by {
        instantiate(forall (j: uint64) { lo <= j and j < k implies defined(p[j]) }, i) using { lo <= i; i < k; };
        known();
    }
}
int32 pointers(int32 **p, int32 n, int32 k) {
    requires 0 <= k;
    requires k < n;
    owns p[0..n];
    ensures result == 0;
} by {
    have forall (j: int32) { 0 <= j and j < n implies defined(p[j]) } by { known(); }
    have defined(p[k]) by {
        instantiate(forall (j: int32) { 0 <= j and j < n implies defined(p[j]) }, k) using { 0 <= k; k < n; };
        known();
    }
}
```

```expect
pass
```
