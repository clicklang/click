# external allocator contracts return owned storage

```c filename=external_allocator_contract.c
int32 caller() {
    uint8* data;
    data = external_alloc(4);
    data[0] = 7;
    free(data);
    return 7;
}
```

```click
import "external_alloc.interface.click";
verifying "external_allocator_contract.c";

int32 caller() {
    ensures result == 7;
}
```

```expect
pass
```
