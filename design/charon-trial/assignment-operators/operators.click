import click::integer;
verifying "operators.rs";

// Bound the exact products so callers keep the zero-multiplier case.
impl MulAssign<u32> for U32X4 {
    fn mul_assign(&mut self, rhs: u32) {
        requires to_integer(self.0[0]) * to_integer(rhs) <= 4294967295;
        requires to_integer(self.0[1]) * to_integer(rhs) <= 4294967295;
        requires to_integer(self.0[2]) * to_integer(rhs) <= 4294967295;
        requires to_integer(self.0[3]) * to_integer(rhs) <= 4294967295;
        owns self.0[0..4];
        ensures self.0[0] == old(self.0[0]) * rhs;
        ensures self.0[1] == old(self.0[1]) * rhs;
        ensures self.0[2] == old(self.0[2]) * rhs;
        ensures self.0[3] == old(self.0[3]) * rhs;
    } by {
        apply(integer::uint32_multiply_guard_by_integer_bound(self.0[0], rhs));
        apply(integer::uint32_multiply_to_integer(self.0[0], rhs));
        apply(integer::uint32_multiply_guard_by_integer_bound(self.0[1], rhs));
        apply(integer::uint32_multiply_to_integer(self.0[1], rhs));
        apply(integer::uint32_multiply_guard_by_integer_bound(self.0[2], rhs));
        apply(integer::uint32_multiply_to_integer(self.0[2], rhs));
        apply(integer::uint32_multiply_guard_by_integer_bound(self.0[3], rhs));
        apply(integer::uint32_multiply_to_integer(self.0[3], rhs));
        if rhs == 0u32 {
            step_until(function.exit);
            have to_integer(self.0[0]) == to_integer(old(self.0[0]) * rhs);
            have to_integer(self.0[1]) == to_integer(old(self.0[1]) * rhs);
            have to_integer(self.0[2]) == to_integer(old(self.0[2]) * rhs);
            have to_integer(self.0[3]) == to_integer(old(self.0[3]) * rhs);
            close();
        } else {
            step_until(function.exit);
            have to_integer(self.0[0]) == to_integer(old(self.0[0]) * rhs);
            have to_integer(self.0[1]) == to_integer(old(self.0[1]) * rhs);
            have to_integer(self.0[2]) == to_integer(old(self.0[2]) * rhs);
            have to_integer(self.0[3]) == to_integer(old(self.0[3]) * rhs);
            close();
        }
    }
}

fn scaled(words: &mut U32X4, factor: u32) {
    requires to_integer(words.0[0]) * to_integer(factor) <= 4294967295;
    requires to_integer(words.0[1]) * to_integer(factor) <= 4294967295;
    requires to_integer(words.0[2]) * to_integer(factor) <= 4294967295;
    requires to_integer(words.0[3]) * to_integer(factor) <= 4294967295;
    owns words.0[0..4];
    ensures words.0[0] == old(words.0[0]) * factor;
    ensures words.0[1] == old(words.0[1]) * factor;
    ensures words.0[2] == old(words.0[2]) * factor;
    ensures words.0[3] == old(words.0[3]) * factor;
}

impl RemAssign<u32> for U32X4 {
    fn rem_assign(&mut self, quotient: u32) {
        requires quotient != 0u32;
        owns self.0[0..4];
        ensures self.0[0] == old(self.0[0]) % quotient;
        ensures self.0[1] == old(self.0[1]) % quotient;
        ensures self.0[2] == old(self.0[2]) % quotient;
        ensures self.0[3] == old(self.0[3]) % quotient;
    }
}

fn reduced(words: &mut U32X4, divisor: u32) {
    requires divisor != 0u32;
    owns words.0[0..4];
    ensures words.0[0] == old(words.0[0]) % divisor;
    ensures words.0[1] == old(words.0[1]) % divisor;
    ensures words.0[2] == old(words.0[2]) % divisor;
    ensures words.0[3] == old(words.0[3]) % divisor;
}

theorem lane_add_fits(left: uint32, right: uint32) {
    requires left <= 1000u32;
    requires right <= 1000u32;
    ensures to_integer(left) <= to_integer(4294967295u32 - right) by {
        have to_integer(left) + to_integer(right) <= 4294967295 by close() using {
            to_integer(left) <= 1000;
            to_integer(right) <= 1000;
        };
        have to_integer(right) <= 4294967295;
        apply(integer::uint32_subtract_to_integer(4294967295u32, right));
        close() using {
            to_integer(left) + to_integer(right) <= 4294967295;
            to_integer(4294967295u32 - right) == 4294967295 - to_integer(right);
        };
    }
}

theorem lane_add_value(left: uint32, right: uint32) {
    requires left <= 1000u32;
    requires right <= 1000u32;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have to_integer(left) + to_integer(right) <= 4294967295 by close() using {
            to_integer(left) <= 1000;
            to_integer(right) <= 1000;
        };
        apply(integer::uint32_add_to_integer(left, right));
    }
}

impl AddAssign<&U32X4> for U32X4 {
    fn add_assign(&mut self, other: &U32X4) {
        requires separate(memory(self.0[0..4]), memory(other.0[0..4]));
        views other.0[0..4];
        requires self.0[0] <= 1000u32;
        requires other.0[0] <= 1000u32;
        requires self.0[1] <= 1000u32;
        requires other.0[1] <= 1000u32;
        requires self.0[2] <= 1000u32;
        requires other.0[2] <= 1000u32;
        requires self.0[3] <= 1000u32;
        requires other.0[3] <= 1000u32;
        owns self.0[0..4];
        ensures self.0[0] == old(self.0[0]) + old(other.0[0]);
        ensures other.0[0] == old(other.0[0]);
        ensures self.0[1] == old(self.0[1]) + old(other.0[1]);
        ensures other.0[1] == old(other.0[1]);
        ensures self.0[2] == old(self.0[2]) + old(other.0[2]);
        ensures other.0[2] == old(other.0[2]);
        ensures self.0[3] == old(self.0[3]) + old(other.0[3]);
        ensures other.0[3] == old(other.0[3]);
    } by {
        apply(lane_add_value(self.0[0], other.0[0]));
        apply(lane_add_value(self.0[1], other.0[1]));
        apply(lane_add_value(self.0[2], other.0[2]));
        apply(lane_add_value(self.0[3], other.0[3]));
        // Check each addition at its reads and frame the viewed lanes across its store.
        step_until(statement(0).region(8).entry);
        have statement(0).region(3).result == old(self.0[0]);
        have statement(0).region(7).result == old(other.0[0]);
        have statement(0).region(3).result <= 1000u32 by close() using {
            statement(0).region(3).result == old(self.0[0]);
            old(self.0[0]) <= 1000u32;
        };
        have statement(0).region(7).result <= 1000u32 by close() using {
            statement(0).region(7).result == old(other.0[0]);
            old(other.0[0]) <= 1000u32;
        };
        apply(lane_add_fits(statement(0).region(3).result, statement(0).region(7).result));
        step_until(statement(0).region(13).entry);
        step();
        have separate(statement(0).region(13).footprint, memory(other.0[0..4]));
        have separate(statement(0).region(13).footprint, memory(other.0[0..1]));
        have other.0[0] == at(statement(0).region(13).entry, other.0[0]) by {
            preserve(memory(other.0[0..1]), statement(0).region(13));
        }
        have separate(statement(0).region(13).footprint, memory(other.0[1..2]));
        have other.0[1] == at(statement(0).region(13).entry, other.0[1]) by {
            preserve(memory(other.0[1..2]), statement(0).region(13));
        }
        have separate(statement(0).region(13).footprint, memory(other.0[2..3]));
        have other.0[2] == at(statement(0).region(13).entry, other.0[2]) by {
            preserve(memory(other.0[2..3]), statement(0).region(13));
        }
        have separate(statement(0).region(13).footprint, memory(other.0[3..4]));
        have other.0[3] == at(statement(0).region(13).entry, other.0[3]) by {
            preserve(memory(other.0[3..4]), statement(0).region(13));
        }
        step_until(statement(1).region(8).entry);
        have statement(1).region(3).result == old(self.0[1]);
        have statement(1).region(7).result == old(other.0[1]);
        have statement(1).region(3).result <= 1000u32 by close() using {
            statement(1).region(3).result == old(self.0[1]);
            old(self.0[1]) <= 1000u32;
        };
        have statement(1).region(7).result <= 1000u32 by close() using {
            statement(1).region(7).result == old(other.0[1]);
            old(other.0[1]) <= 1000u32;
        };
        apply(lane_add_fits(statement(1).region(3).result, statement(1).region(7).result));
        step_until(statement(1).region(13).entry);
        step();
        have separate(statement(1).region(13).footprint, memory(other.0[0..4]));
        have separate(statement(1).region(13).footprint, memory(other.0[0..1]));
        have other.0[0] == at(statement(1).region(13).entry, other.0[0]) by {
            preserve(memory(other.0[0..1]), statement(1).region(13));
        }
        have separate(statement(1).region(13).footprint, memory(other.0[1..2]));
        have other.0[1] == at(statement(1).region(13).entry, other.0[1]) by {
            preserve(memory(other.0[1..2]), statement(1).region(13));
        }
        have separate(statement(1).region(13).footprint, memory(other.0[2..3]));
        have other.0[2] == at(statement(1).region(13).entry, other.0[2]) by {
            preserve(memory(other.0[2..3]), statement(1).region(13));
        }
        have separate(statement(1).region(13).footprint, memory(other.0[3..4]));
        have other.0[3] == at(statement(1).region(13).entry, other.0[3]) by {
            preserve(memory(other.0[3..4]), statement(1).region(13));
        }
        step_until(statement(2).region(8).entry);
        have statement(2).region(3).result == old(self.0[2]);
        have statement(2).region(7).result == old(other.0[2]);
        have statement(2).region(3).result <= 1000u32 by close() using {
            statement(2).region(3).result == old(self.0[2]);
            old(self.0[2]) <= 1000u32;
        };
        have statement(2).region(7).result <= 1000u32 by close() using {
            statement(2).region(7).result == old(other.0[2]);
            old(other.0[2]) <= 1000u32;
        };
        apply(lane_add_fits(statement(2).region(3).result, statement(2).region(7).result));
        step_until(statement(2).region(13).entry);
        step();
        have separate(statement(2).region(13).footprint, memory(other.0[0..4]));
        have separate(statement(2).region(13).footprint, memory(other.0[0..1]));
        have other.0[0] == at(statement(2).region(13).entry, other.0[0]) by {
            preserve(memory(other.0[0..1]), statement(2).region(13));
        }
        have separate(statement(2).region(13).footprint, memory(other.0[1..2]));
        have other.0[1] == at(statement(2).region(13).entry, other.0[1]) by {
            preserve(memory(other.0[1..2]), statement(2).region(13));
        }
        have separate(statement(2).region(13).footprint, memory(other.0[2..3]));
        have other.0[2] == at(statement(2).region(13).entry, other.0[2]) by {
            preserve(memory(other.0[2..3]), statement(2).region(13));
        }
        have separate(statement(2).region(13).footprint, memory(other.0[3..4]));
        have other.0[3] == at(statement(2).region(13).entry, other.0[3]) by {
            preserve(memory(other.0[3..4]), statement(2).region(13));
        }
        step_until(statement(3).region(8).entry);
        have statement(3).region(3).result == old(self.0[3]);
        have statement(3).region(7).result == old(other.0[3]);
        have statement(3).region(3).result <= 1000u32 by close() using {
            statement(3).region(3).result == old(self.0[3]);
            old(self.0[3]) <= 1000u32;
        };
        have statement(3).region(7).result <= 1000u32 by close() using {
            statement(3).region(7).result == old(other.0[3]);
            old(other.0[3]) <= 1000u32;
        };
        apply(lane_add_fits(statement(3).region(3).result, statement(3).region(7).result));
        step_until(statement(3).region(13).entry);
        step();
        have separate(statement(3).region(13).footprint, memory(other.0[0..4]));
        have separate(statement(3).region(13).footprint, memory(other.0[0..1]));
        have other.0[0] == at(statement(3).region(13).entry, other.0[0]) by {
            preserve(memory(other.0[0..1]), statement(3).region(13));
        }
        have separate(statement(3).region(13).footprint, memory(other.0[1..2]));
        have other.0[1] == at(statement(3).region(13).entry, other.0[1]) by {
            preserve(memory(other.0[1..2]), statement(3).region(13));
        }
        have separate(statement(3).region(13).footprint, memory(other.0[2..3]));
        have other.0[2] == at(statement(3).region(13).entry, other.0[2]) by {
            preserve(memory(other.0[2..3]), statement(3).region(13));
        }
        have separate(statement(3).region(13).footprint, memory(other.0[3..4]));
        have other.0[3] == at(statement(3).region(13).entry, other.0[3]) by {
            preserve(memory(other.0[3..4]), statement(3).region(13));
        }
        step_until(function.exit);
        have to_integer(self.0[0]) == to_integer(old(self.0[0]) + old(other.0[0]));
        have to_integer(self.0[1]) == to_integer(old(self.0[1]) + old(other.0[1]));
        have to_integer(self.0[2]) == to_integer(old(self.0[2]) + old(other.0[2]));
        have to_integer(self.0[3]) == to_integer(old(self.0[3]) + old(other.0[3]));
        have other.0[0] == old(other.0[0]);
        have other.0[1] == old(other.0[1]);
        have other.0[2] == old(other.0[2]);
        have other.0[3] == old(other.0[3]);
        close();
    }
}

fn added(words: &mut U32X4, other: &U32X4) {
    requires separate(memory(words.0[0..4]), memory(other.0[0..4]));
    views other.0[0..4];
    requires words.0[0] <= 1000u32;
    requires other.0[0] <= 1000u32;
    requires words.0[1] <= 1000u32;
    requires other.0[1] <= 1000u32;
    requires words.0[2] <= 1000u32;
    requires other.0[2] <= 1000u32;
    requires words.0[3] <= 1000u32;
    requires other.0[3] <= 1000u32;
    owns words.0[0..4];
    ensures words.0[0] == old(words.0[0]) + old(other.0[0]);
    ensures other.0[0] == old(other.0[0]);
    ensures words.0[1] == old(words.0[1]) + old(other.0[1]);
    ensures other.0[1] == old(other.0[1]);
    ensures words.0[2] == old(words.0[2]) + old(other.0[2]);
    ensures other.0[2] == old(other.0[2]);
    ensures words.0[3] == old(words.0[3]) + old(other.0[3]);
    ensures other.0[3] == old(other.0[3]);
}

fn local(a: u32, b: u32) -> u32 { requires a <= 1000u32; requires b <= 1000u32; ensures result == ((a * 2u32 % 7u32) ^ (b * 2u32 % 7u32)); }
