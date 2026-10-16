# Arithmetic after a native seed rewrite retains a printable goal
```c filename=render.c
unsigned long seed(unsigned long word, unsigned long len) {
 word &= 65535UL;
 while (len > 0) { --len; }
 return word;
}
```
```click
import click::integer;
import click::machine_integer;
verifying "render.c";
function decode(word: uint64) -> uint64 { word & 65535u64 }
function count(total: uint64, remaining: uint64) -> int32 { (int32)(uint32)(total - remaining) }
function observe(n: int32, value: Integer) -> Integer { value }
uint64 seed(uint64 word, uint64 len) {
 requires len <= 15u64;
 requires observe(0, to_integer(decode(word))) == to_integer(decode(word));
 ensures result == decode(old(word));
} by {
 unfold(decode(word));
 execute_until(loop(0));
 loop {
  decreases to_integer(len);
  invariant to_integer(len) <= 15;
  invariant word == decode(old(word));
  initialize by {
   apply(uint64_less_equal_to_integer(len, 15u64));
   have count(old(len), len) == 0 by { unfold(count(old(len), len)); simp(); }
   have word == decode(old(word)) by simp();
   have to_integer(word) == observe(count(old(len), len), to_integer(decode(old(word)))) by {
    rewrite(count(old(len), len) == 0);
    rewrite(word == decode(old(word)));
    arithmetic() using { observe(0, to_integer(decode(old(word)))) == to_integer(decode(old(word))); };
   }
   simp();
  }
  preserve by {
   have len > 0u64 by assumption();
   have 0u64 < len by {
    if 0u64 < len { assumption(); } else {
     have 0u64 <= len by normalize();
     apply(uint64_less_equal_and_not_less_than_implies_equal(0u64, len));
     have len == 0u64 by { rewrite(0u64 == len); normalize(); }
     have not (len > 0u64) by { rewrite(len == 0u64); normalize(); }
     contradiction(len > 0u64);
    }
   }
   apply(uint64_to_integer_bounds(len));
   apply(uint64_less_than_to_integer(0u64, len));
   have to_integer(1u64) <= to_integer(len) by arithmetic() using { to_integer(0u64) < to_integer(len); };
   apply(uint64_to_integer_less_equal_implies_less_equal(1u64, len));
   apply(uint64_subtract_to_integer(len, 1u64));
   mark before_decrement;
   step();
   have to_integer(len) == at(before_decrement, to_integer(len)) - 1 by assumption();
   have to_integer(len) <= 15 by arithmetic() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; at(before_decrement, to_integer(len)) <= 15; };
   have 0 <= to_integer(len) by arithmetic() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; to_integer(1u64) <= at(before_decrement, to_integer(len)); };
   have to_integer(len) < at(before_decrement, to_integer(len)) by arithmetic() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; };
   close_invariants() by { simp(); }
  }
 }
 execute(); simp();
}
```
```expect
pass
```
