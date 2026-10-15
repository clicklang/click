# Backing ranges rejoin after field-preserving modular calls

```c filename=probe.c
struct owner {
    int32 first_len;
    int32 second_len;
    int32* first_data;
    int32* second_data;
};
void set_first(struct owner* owner) { owner->first_data[0] = 1; }
void set_second(struct owner* owner) { owner->second_data[0] = 2; }
void probe(struct owner* owner) { set_first(owner); set_second(owner); }
```
```click
verifying "probe.c";
resource buffers(owner: struct owner*) {
    owns owner->first_len;
    owns owner->second_len;
    owns owner->first_data;
    owns owner->second_data;
    owns owner->first_data[0..owner->first_len];
    owns owner->second_data[0..owner->second_len];
    fact 1 <= owner->first_len;
    fact 1 <= owner->second_len;
    fact separate(memory(*owner), memory(owner->first_data[0..owner->first_len]));
    fact separate(memory(*owner), memory(owner->second_data[0..owner->second_len]));
}
void set_first(struct owner* owner) {
    requires separate(memory(*owner), memory(owner->first_data[0..owner->first_len]));
    views owner->first_len;
    views owner->second_len;
    views owner->first_data;
    views owner->second_data;
    owns owner->first_data[0..1];
    ensures owner->first_len == old(owner->first_len);
    ensures owner->second_len == old(owner->second_len);
    ensures owner->first_data == old(owner->first_data);
    ensures owner->second_data == old(owner->second_data);
} by { execute(); simp(); }
void set_second(struct owner* owner) {
    requires separate(memory(*owner), memory(owner->second_data[0..owner->second_len]));
    views owner->first_len;
    views owner->second_len;
    views owner->first_data;
    views owner->second_data;
    owns owner->second_data[0..1];
    ensures owner->first_len == old(owner->first_len);
    ensures owner->second_len == old(owner->second_len);
    ensures owner->first_data == old(owner->first_data);
    ensures owner->second_data == old(owner->second_data);
} by { execute(); simp(); }
void probe(struct owner* owner) {
    owns buffers(owner);
} by {
    unfold(buffers(owner));
    step(); step();
    fold(buffers(owner));
    execute(); simp();
}
```
```expect
pass
```
