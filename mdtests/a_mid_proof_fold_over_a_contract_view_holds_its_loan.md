# A mid-proof fold over a contract's view holds its loan

`first` receives `views p[0..1]` by contract. Folding `cell(p)`, whose body
views that cell, packages the borrowed view into an owned head, and the fold
places a hold on the view's loan so the head's body cannot outlive the
borrow. The fold is allowed anywhere in the proof, not only at a `produces`
return: `first` folds and unfolds before executing, and `lend` folds, lends
the head to a callee that views `cell(p)`, and unfolds it after the call.

```c filename=a_mid_proof_fold_over_a_contract_view_holds_its_loan.c
int read_cell(int *p);

int first(int p[])
{
	return p[0];
}

int lend(int *p)
{
	return read_cell(p);
}
```

```click
resource cell(p: int32*) {
    views p[0..1];
}

verifying "a_mid_proof_fold_over_a_contract_view_holds_its_loan.c";

extern int32 read_cell(int32* p) {
    views cell(p);
    ensures true;
}

int32 first(int32 p[]) {
    views p[0..1];
    ensures result == p[0];
} by {
    fold(cell(p));
    unfold(cell(p));
    execute();
    simp();
}

int32 lend(int32* p) {
    views p[0..1];
    ensures true;
} by {
    fold(cell(p));
    step();
    unfold(cell(p));
    execute();
}
```

```expect
pass
```
