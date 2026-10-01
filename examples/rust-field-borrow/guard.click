verifying "guard.rs";

void Guard_drop(struct Guard* self) {
    requires separate(memory(object(self)), memory(self->slot[0..1]));
    owns &self->slot;
    owns self->saved;
    owns self->slot[0..1];
    ensures self->slot == old(self->slot);
    ensures self->saved == old(self->saved);
    ensures self->slot[0] == old(self->saved);
} by {
    execute();
    simp();
}

void cleanup(int32* value) {
    owns value[0..1];
    ensures value[0] == 42;
} by {
    execute();
    simp();
}
