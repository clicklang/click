resource pool_slot(pool: struct pool*) {}
resource pool_object(pool: struct pool*, object: struct object*) { owns object(object); }
resource pool_storage(pool: struct pool*) {
    owns object(pool);
    owns authority(pool_slot(pool));
    owns authority(pool_object(pool, _));
}
resource pool_control(pool: struct pool*) {
    owns object(pool);
    owns authority(pool_slot(pool));
    owns authority(pool_object(pool, _));
    fact 0 <= pool->checked_out;
    fact pool->checked_out == count(pool_object(pool, _));
    fact pool->capacity == pool->checked_out + count(pool_slot(pool));
}
predicate valid_pool(pool: struct pool*) {
    0 <= pool->checked_out and
    pool->checked_out == count(pool_object(pool, _)) and
    pool->capacity == pool->checked_out + count(pool_slot(pool))
}
verifying "../bounded-pool/pool_init.c";
verifying "../bounded-pool/pool_destroy.c";
verifying "../bounded-pool/pool_zero_pipeline.c";
verifying "../bounded-pool/pool_checkout.c";
void pool_init(struct pool* pool, int32 capacity) {
    consumes pool_storage(pool);
    requires 0 <= capacity;
    requires count(pool_slot(pool)) == 0;
    requires count(pool_object(pool, _)) == 0;
    produces pool_control(pool);
    produces capacity of pool_slot(pool);
    ensures pool->capacity == capacity;
    ensures pool->checked_out == 0;
    ensures count(pool_object(pool, _)) == 0;
    ensures valid_pool(pool);
} by {
    unfold(pool_storage(pool));
    step(); step();
    fold(capacity of pool_slot(pool));
    fold(pool_control(pool));
    execute(); unfold(valid_pool); simp();
}
void pool_destroy(struct pool* pool) {
    consumes pool_control(pool);
    consumes pool->capacity of pool_slot(pool);
    requires pool->checked_out == 0;
    produces object(pool);
    ensures pool->checked_out == 0;
    ensures pool->capacity == 0;
    ensures count(pool_slot(pool)) == 0;
    ensures count(pool_object(pool, _)) == 0;
    ensures valid_pool(pool);
} by {
    unfold(pool_control(pool));
    have count(pool_object(pool, _)) == 0 by simp;
    have pool->capacity == count(pool_slot(pool)) by simp;
    unfold(pool->capacity of pool_slot(pool));
    have count(pool_slot(pool)) == 0 by simp;
    step();
    unfold(authority(pool_slot(pool)));
    unfold(authority(pool_object(pool, _)));
    execute(); unfold(valid_pool); simp();
}
void pool_zero_pipeline(struct pool* pool) {
    consumes pool_storage(pool);
    requires count(pool_slot(pool)) == 0;
    requires count(pool_object(pool, _)) == 0;
    produces object(pool);
    ensures pool->checked_out == 0;
    ensures pool->capacity == 0;
    ensures count(pool_slot(pool)) == 0;
    ensures count(pool_object(pool, _)) == 0;
    ensures valid_pool(pool);
} by {
    step();
    unfold(pool_control(pool));
    have pool->capacity == count(pool_slot(pool)) by simp;
    have count(pool_object(pool, _)) == 0 by simp;
    fold(pool_control(pool));
    step();
    execute(); unfold(valid_pool); simp();
}
