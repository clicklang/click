import click::separation;

verifying "slices.rs";
theorem byte_reflexive(x: uint8) { ensures x == x by { close(); } }
fn length(bytes: &[u8]) -> usize {
    ensures result == bytes.len();
}
fn read(bytes: &[u8], index: usize) -> u8 {
    requires bytes.len() <= 2147483647u64;
    requires index < bytes.len();
    views bytes[0..bytes.len()];
    ensures result == old(bytes[index]);
}
fn write(bytes: &mut [u8], index: usize, value: u8) {
    requires bytes.len() <= 2147483647u64;
    requires index < bytes.len();
    owns bytes[0..bytes.len()];
    ensures bytes[index] == value;
}
fn alias(bytes: &mut [u8], index: usize) -> u8 {
    requires bytes.len() <= 2147483647u64;
    requires index < bytes.len();
    owns bytes[0..bytes.len()];
    ensures result == old(bytes[index]);
} by {
    step_until(function.exit);
    have defined(old(bytes[index]));
    have result == old(bytes[index]) by { apply(byte_reflexive(old(bytes[index]))); close(); }
    close();
}

fn write_read(bytes: &mut [u8], index: usize, value: u8) -> u8 {
    requires bytes.len() <= 2147483647u64;
    requires index < bytes.len();
    owns bytes[0..bytes.len()];
    ensures result == value;
    ensures bytes[index] == value;
} by {
    step_until(function.exit);
    have result == bytes[index];
    close();
}

impl Drop for Guard {
    fn drop(&mut self) {
        requires separate(memory(*self), memory(self.slot[0..1]));
        owns self.slot;
        owns self.saved;
        owns *self.slot;
        ensures self.slot == old(self.slot);
        ensures self.saved == old(self.saved);
        ensures *self.slot == old(self.saved);
    }
}

fn guarded_read(value: &mut i32, bytes: &[u8], index: usize) -> u32 {
    requires bytes.len() <= 2147483647u64;
    requires index < bytes.len();
    requires separate(memory(value[0..1]), memory(bytes[0..bytes.len()]));
    owns value[0..1];
    views bytes[0..bytes.len()];
    ensures result == old(bytes[index] as uint32);
    ensures value[0] == old(value[0]);
} by {
    step_until(region(3).entry); step();
    have separate(memory((&guard.saved)[0..1]), memory(bytes[0..bytes.len()])) by { close(); }
    step_until(statement(2).entry);
    have bytes[index] == old(bytes[index]) by {
        apply(byte_reflexive(old(bytes[index])));
        close();
    }
    have contains(memory(bytes[0..bytes.len()]), memory(bytes[index])) by {
        apply(separation::contains_element(bytes.as_ptr(), 0u64, bytes.len(), index));
    }
    have separate(memory(value[0..1]), memory(bytes[index])) by {
        apply(separation::contains_refl(memory(value[0..1])));
        apply(separation::separate_restrict(memory(value[0..1]), memory(bytes[0..bytes.len()]), memory(value[0..1]), memory(bytes[index])));
    }
    have guard.slot == value by { close(); }
    have separate(memory(guard.slot[0..1]), memory(bytes[index])) by {
        rewrite(guard.slot, value);
        close();
    }
    mark write_entry;
    step_until(statement(3).entry);
    have separate(statement(2).region(2).footprint, memory(bytes[index])) by {
        close() using { at(write_entry, separate(memory(guard.slot[0..1]), memory(bytes[index]))); };
    }
    have bytes[index] == at(write_entry, bytes[index]) by {
        preserve(memory(bytes[index]), statement(2).region(2));
    }
    have bytes[index] == old(bytes[index]) by {
        rewrite(bytes[index], at(write_entry, bytes[index]));
        close();
    }
    step_until(function.exit);
    have index <= 2147483647u64 by { close() using { index < bytes.len(); bytes.len() <= 2147483647u64; }; }
    have 0 <= index as uint32 as int32 by { close() using { index <= 2147483647u64; }; }
    have (index as uint32 as int32) < bytes.len() as uint32 as int32 by { close() using { index < bytes.len(); bytes.len() <= 2147483647u64; }; }
    have at(statement(3).call(read, 0).entry, bytes[index]) == old(bytes[index]) by {
        close();
    }
    have statement(3).call(read, 0).result == at(statement(3).call(read, 0).entry, bytes[index]) by { close(); }
    have result == old(bytes[index] as uint32) by {
        rewrite(statement(3).call(read, 0).result, at(statement(3).call(read, 0).entry, bytes[index]));
        rewrite(at(statement(3).call(read, 0).entry, bytes[index]), old(bytes[index]));
        close();
    }
    close();
}
