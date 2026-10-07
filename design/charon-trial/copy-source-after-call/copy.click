verifying "copy.rs";
void __rust_q_I22_copy_source_after_call_I3_set(struct __rust_q_I22_copy_source_after_call_I5_Words* words, uint32 value) {
 owns words->_0[0..4]; ensures words->_0[0] == value;
} by { execute(); simp(); }
void __rust_q_I22_copy_source_after_call_I7_consume(struct __rust_q_I22_copy_source_after_call_I5_Words* target, struct __rust_q_I22_copy_source_after_call_I5_Words other) {
 owns target->_0[0..4]; ensures target->_0[0] == old(other._0[0]);
} by { execute(); simp(); }
uint32 __rust_q_I22_copy_source_after_call_I6_caller(uint32 value) {
 ensures result == value;
 } by {
 execute_until(assignment(__rust_mir_14, 0));
 have target._0[0] == value by { simp(); }
 execute();
 simp();
}
