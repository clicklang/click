# Float pointer casts retain their address and read width

```c filename=contract_float_pointer_casts.c
float* next32(float* p) { return p + 1; }
double* next64(double* p) { return p + 1; }
float read32(float* p) { return *p; }
double read64(double* p) { return *p; }
```

```click
verifying "contract_float_pointer_casts.c";

float* next32(float* p) {
    views p[0..2];
    ensures result == (p as (uint8 *) as (void *) as (float *)) + 1;
    ensures result as (uint8 *) == p as (uint8 *) + 4;
}

double* next64(double* p) {
    views p[0..2];
    ensures result == (p as (uint8 *) as (void *) as (double *)) + 1;
    ensures result as (uint8 *) == p as (uint8 *) + 8;
}

float read32(float* p) {
    views *p;
    requires isfinite(*p);
    ensures result == *(p as (uint8 *) as (void *) as (float *));
} by { step(); solve(); }

double read64(double* p) {
    views *p;
    requires isfinite(*p);
    ensures result == (p as (uint8 *) as (void *) as (double *))[0];
} by { step(); solve(); }
```

```expect
pass
```
