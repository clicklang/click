# Function-type typedefs preserve callback signatures

```c filename=callbacks.c
typedef int unary(int);
typedef int (parenthesized)(int);
struct holder { parenthesized *invoke; };

int identity(int value) { return value; }

int apply(unary *callback, int value) {
    return callback(value);
}

int use_field(struct holder *holder, int value) {
    holder->invoke = &identity;
    parenthesized *local = holder->invoke;
    return local(value);
}
```

```click
verifying "callbacks.c";

contract int Identity(int value) {
    ensures result == value;
}

int identity(int value) {
    ensures result == value;
}

int apply(unary *callback, int value) {
    requires Identity(callback);
    ensures result == value;
}

int use_field(struct holder *holder, int value) {
    owns holder[0..1];
    ensures result == value;
}
```

```expect
pass
```
