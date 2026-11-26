# byte count of two merged branches matches the C count

Two `if` statements each add one to a counter when a byte equals `x`.
The first join records its conditional count. Each arm of the second branch
uses that count and its byte comparison to normalize the unfolded
`bytes::count` fold, then the second join carries the result to the return.

```c filename=byte_count_of_two_merged_branches_matches_the_c_count.c
int32 count_byte2(uint8 p[], uint8 x) {
    int32 count;
    count = 0;
    if (p[0] == x) {
        count = count + 1;
    }
    if (p[1] == x) {
        count = count + 1;
    }
    return count;
}
```

```click
import click::bytes;
verifying "byte_count_of_two_merged_branches_matches_the_c_count.c";

int32 count_byte2(uint8 p[], uint8 x) {
    views p[0..2];
    ensures result == bytes::count(p, 0, 2, x) by {
        step();
        step();
        mark first;
        branch ensuring {
            fact count == (if at(first, p[0]) == at(first, x) { 1 } else { 0 });
        } {
            true => {
                step();
                have count == (if at(first, p[0]) == at(first, x) { 1 } else { 0 }) by {
                    have (if at(first, p[0]) == at(first, x) { 1 } else { 0 }) == 1 by close();
                    rewrite(if at(first, p[0]) == at(first, x) { 1 } else { 0 }, 1);
                    close();
                }
            }
            false => {
                have count == (if at(first, p[0]) == at(first, x) { 1 } else { 0 }) by {
                    have (if at(first, p[0]) == at(first, x) { 1 } else { 0 }) == 0 by close();
                    rewrite(if at(first, p[0]) == at(first, x) { 1 } else { 0 }, 0);
                    close();
                }
            }
        }
        mark second;
        branch ensuring { fact count == bytes::count(p, 0, 2, x); } {
            true => {
                step();
                have count == bytes::count(p, 0, 2, x) by {
                    unfold(bytes::count(p, 0, 2, x));
                    rewrite(at(second, count), (if at(first, p[0]) == at(first, x) { 1 } else { 0 }));
                    have p[1] == x by close();
                    have (if p[1] == x { 1 } else { 0 }) == 1 by close();
                    rewrite(if p[1] == x { 1 } else { 0 }, 1);
                    close();
                }
            }
            false => {
                have count == bytes::count(p, 0, 2, x) by {
                    unfold(bytes::count(p, 0, 2, x));
                    rewrite(at(second, count), (if at(first, p[0]) == at(first, x) { 1 } else { 0 }));
                    have p[1] != x by close();
                    have (if p[1] == x { 1 } else { 0 }) == 0 by close();
                    rewrite(if p[1] == x { 1 } else { 0 }, 0);
                    close();
                }
            }
        }
        step();
        close();
    }
}
```

```expect
pass
```
