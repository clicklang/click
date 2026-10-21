arithmetic "integer";

verifying "rep_copy.c";
verifying "rep_copy_symbolic.c";
verifying "use_copy.c";

int f() {
    ensures result == 18 or result == -1;
} by {
    execute();
    simp();
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
    have to_integer((uint32)p[0]) == to_integer(p[0]) by {
        arithmetic_certificate rules {
            premise 0: 0 <= to_integer(p[0]) => 0 <= to_integer(p[0]);
            premise 1: to_integer(p[0]) <= 1000 => to_integer(p[0]) <= 1000;
            integer_cast_identity bounds [0, 1] => to_integer((uint32)p[0]) == to_integer(p[0]);
            conclusion 0;
        }
    }
    have to_integer(tag + (uint32)p[0]) == to_integer(tag) + to_integer((uint32)p[0]) by auto();
    have 0 <= to_integer(tag + (uint32)p[0]) by auto();
    have to_integer(tag + (uint32)p[0]) <= 2000 by auto();
    have to_integer((int32)(tag + (uint32)p[0])) == to_integer(tag + (uint32)p[0]) by {
        arithmetic_certificate rules {
            premise 0: 0 <= to_integer(tag + (uint32)p[0]) => 0 <= to_integer(tag + (uint32)p[0]);
            premise 1: to_integer(tag + (uint32)p[0]) <= 2000 => to_integer(tag + (uint32)p[0]) <= 2000;
            integer_cast_identity bounds [0, 1] => to_integer((int32)(tag + (uint32)p[0])) == to_integer(tag + (uint32)p[0]);
            conclusion 0;
        }
    }
    execute();
    auto();
}

int use_copy() {
    ensures result == 18 or result == 0;
} by {
    step();
    step();
    if copied == 18 {
        execute();
        simp();
    } else {
        have copied == -1 by {
            cases {
                copied == 18 => {
                    contradiction(copied == 18);
                }
                copied == -1 => {
                    assumption();
                }
            }
        }
        execute();
        simp();
    }
}
