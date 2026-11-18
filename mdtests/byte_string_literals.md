# Byte strings are structural lists of exact bytes

```click
theorem exact_bytes() {
    ensures b"" == List<uint8>::Nil by normalize();
    ensures b"\"\\\n\r\t\0\xff'\xc3\xa9" ==
        List::Cons(34u8, List::Cons(92u8, List::Cons(10u8, List::Cons(13u8,
        List::Cons(9u8, List::Cons(0u8, List::Cons(255u8, List::Cons(39u8,
        List::Cons(195u8, List::Cons(169u8, List<uint8>::Nil))))))))))
        by normalize();
}
```

```expect
pass
```
