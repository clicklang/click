verifying "loop.rs";

void Guard_drop(struct Guard* self) {
    requires separate(memory(object(self)), memory(self->slot[0..1]));
    owns &self->slot;
    owns self->saved;
    owns self->slot[0..1];
    ensures self->slot == old(self->slot);
    ensures self->saved == old(self->saved);
    ensures self->slot[0] == old(self->saved);
} by {
    execute(); simp();
}

int32 guarded_walk(int32* value, int32 n) {
    requires n >= 0;
    owns value[0..1];
    ensures result == n;
    ensures value[0] == old(value[0]);
} by {
    execute_until(loop(0));
    loop {
        decreases n - i;
        owns value[0..1];
        views &guard.slot;
        views guard.saved;
        invariant 0 <= i and i <= n;
        invariant separate(memory(&guard.slot), memory(value[0..1]));
        invariant separate(memory(guard.saved), memory(value[0..1]));
        invariant guard.slot == value;
        invariant guard.saved == old(value[0]);
    }
    execute(); simp();
}

int32 final_header(int32 n) {
    requires n >= 0;
    ensures result == n;
} by {
    execute_until(loop(0));
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
    }
    execute(); simp();
}
