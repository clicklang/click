# A returned widened sum has an ordinary observation identity

```c filename=wide.c
long add_byte(unsigned sum, unsigned char byte) {
    unsigned word = (unsigned)byte;
    long wide = (long)sum + (long)word;
    return wide;
}
```

```click
verifying "wide.c";
int64 add_byte(uint32 sum, uint8 byte) {
    requires sum <= 4294967040u32;
    ensures result <= 4294967295i64 by {
        step_until(function.exit);
        have to_integer(result) == to_integer(sum as int64) + to_integer((byte as uint32) as int64) by {
            have 0 <= to_integer(sum as int64) by known();
            have to_integer(sum as int64) <= 4294967295 by known();
            have 0 <= to_integer((byte as uint32) as int64) by known();
            have to_integer((byte as uint32) as int64) <= 255 by known();
            have -9223372036854775808 <= to_integer(sum as int64) + to_integer((byte as uint32) as int64) by {
                solve() using {0 <= to_integer(sum as int64); 0 <= to_integer((byte as uint32) as int64);};
            }
            have to_integer(sum as int64) + to_integer((byte as uint32) as int64) <= 9223372036854775807 by {
                solve() using {to_integer(sum as int64) <= 4294967295; to_integer((byte as uint32) as int64) <= 255;};
            }
            known();
        }
        solve() using {to_integer(result) == to_integer(sum as int64) + to_integer((byte as uint32) as int64); sum <= 4294967040u32; (byte as uint32) <= 255u32;};
    }
}
```

```expect
pass
```
