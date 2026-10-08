verifying "trial.rs";

void Guard_drop(struct Guard* self) {
    requires separate(memory(*self), memory(self->slot[0..1]));
    owns self->slot;
    owns self->saved;
    owns self->slot[0..1];
    ensures self->slot == old(self->slot);
    ensures self->saved == old(self->saved);
    ensures self->slot[0] == old(self->saved);
} by {
    execute();
    simp();
}

uint16 increment(uint16 x) {
    requires x < 65535;
    ensures result == x + 1;
} by {
    execute();
    simp();
}

uint16 guarded_increment(uint16 x, int32* value, bool early) {
    requires x < 65535;
    owns value[0..1];
    ensures result == x + 1;
    ensures value[0] == old(value[0]);
} by {
    execute();
    simp();
}
