# A typedef may define an anonymous enum

jsmn declares its token kinds as `typedef enum { ... } jsmntype_t;`, and
heatshrink and uzlib declare their states the same way. The typedef defines the
enumeration it names; its constants and objects behave as a tagged enum's.
The enumeration is jsmn's, unchanged.

```c filename=jsmn_type.c
typedef enum {
  JSMN_UNDEFINED = 0,
  JSMN_OBJECT = 1 << 0,
  JSMN_ARRAY = 1 << 1,
  JSMN_STRING = 1 << 2,
  JSMN_PRIMITIVE = 1 << 3
} jsmntype_t;

int is_container(jsmntype_t type)
{
	return type == JSMN_OBJECT || type == JSMN_ARRAY;
}
```

```click
verifying "jsmn_type.c";

int32 is_container(uint32 type) {
    requires type == 2;
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
