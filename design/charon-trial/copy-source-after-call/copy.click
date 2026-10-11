verifying "copy.rs";
fn copy_source_after_call::set(words: &mut copy_source_after_call::Words, value: u32) {
 owns words.0[0..4]; ensures words.0[0] == value;
} by { execute(); simp(); }
fn copy_source_after_call::consume(target: &mut copy_source_after_call::Words, other: copy_source_after_call::Words) {
 owns target.0[0..4]; ensures target.0[0] == old(other.0[0]);
} by { execute(); simp(); }
fn copy_source_after_call::caller(value: u32) -> u32 {
 ensures result == value;
 } by {
 execute_until(assignment(__rust_mir_14, 0));
 have target.0[0] == value;
 execute();
 simp();
}
