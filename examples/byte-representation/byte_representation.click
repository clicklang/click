verifying "rep_copy.c";
verifying "rep_copy_symbolic.c";
verifying "use_copy.c";

int f() {
    ensures result == 18 or result == -1;
}

int32 g(uint32 tag, int32 *p, int32 **restored) {
    views p[0..1];
    owns restored[0..1];
    requires tag <= 1000;
    requires 0 <= p[0];
    requires p[0] <= 1000;
    ensures result == -1 or result == tag + p[0];
    ensures result == -1 or restored[0] == p;
} by {
    have to_integer(p[0] as uint32) == to_integer(p[0]) by {
        solve() using { 0 <= to_integer(p[0]); to_integer(p[0]) <= 1000; };
    }
    have to_integer(tag + p[0] as uint32) == to_integer(tag) + to_integer(p[0] as uint32);
    have 0 <= to_integer(tag + p[0] as uint32);
    have to_integer(tag + p[0] as uint32) <= 2000;
    have to_integer((tag + p[0] as uint32) as int32) == to_integer(tag + p[0] as uint32) by {
        solve() using { 0 <= to_integer(tag + p[0] as uint32); to_integer(tag + p[0] as uint32) <= 2000; };
    }
    step();
    step();
    branch {
        step_until(function.exit);
        solve();
    } else {}
    have separate(memory((src as (uint8*))[0..16]), memory(p[0..1])) by { solve(); }
    step();
    step();
    branch {
        step_until(function.exit);
        solve();
    } else {}
    have separate(memory(buf[0..16]), memory(p[0..1])) by { solve(); }
    step();
    step();
    branch {
        step_until(function.exit);
        solve();
    } else {}
    have separate(memory((dst as (uint8*))[0..16]), memory(p[0..1])) by { solve(); }
}

int use_copy() {
    ensures result == 18 or result == 0;
} by {
    step();
    step();
    step();
    if copied == 18 {
    } else {
        have copied == -1 by {
            cases {
                copied == 18 => {
                    contradiction(copied == 18);
                }
                copied == -1 => {
                    known();
                }
            }
        }
    }
}
