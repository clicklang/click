resource cell(p: int32*) {
    field value: int32;
    owns *p;
    fact *p == value;
}
tactic rename_cell(p: int32*) {
    consumes before: cell(p);
    produces after: cell(p);
    ensures after.value == old(before.value);
} by {
    unfold(before);
    let after = fold(cell(p), { value: *p });
}
