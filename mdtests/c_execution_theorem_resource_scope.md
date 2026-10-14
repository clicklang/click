# Execution conclusions bind their selected contract's resources

These contracts reuse parameter names for different resource families. Each
execution theorem opens the family selected by its own `as` map, including
when a later contract has different fields and child slots.

```c filename=resource_scope.c
void noop(int32* p) { }
```

```click
verifying "resource_scope.c";
spec enum Model { Empty, Node(int32), }
resource Cell(p: int32*) { field value: int32; owns p[0]; fact p[0] == value; }
resource Input(p: int32*) {
    field model: Model;
    match model {
        Model::Empty => { fact p == 0; },
        Model::Node(value) => {
            owns child: Cell(p);
            fact child.value == value;
            fact p != 0;
        },
    }
}
resource Output(p: int32*) { field value: int32; owns p[0]; fact p[0] == value; }
resource Other(p: int32*) { field revision: int32; owns p[0]; fact p[0] == revision; }
void noop(int32* p) {
    owns p[0];
    ensures p[0] == old(p[0]);
} by { execute(); simp(); }
contract void Migrated(int32* p) {
    consumes input: Input(p);
    produces output: Output(p);
    requires p != 0;
}
theorem migrate() executes noop(int32* p) {
    ensures Migrated(&noop) as { input: input, output: output } by {
        match input.model {
            Model::Empty => { unfold(input); contradiction(p == 0); },
            Model::Node(value) => {
                let { child: child } = unfold(input);
                unfold(child);
                step(noop(p), {});
                let output = fold(Output(p), { value: value });
                simp();
            },
        }
    }
}
contract void OtherMigration(int32* p) {
    consumes input: Other(p);
    produces output: Output(p);
    ensures output.value == old(input.revision);
}
theorem migrate_other() executes noop(int32* p) {
    ensures OtherMigration(&noop) as { input: before, output: after } by {
        let { revision: value } = unfold(before);
        step(noop(p), {});
        let after = fold(Output(p), { value: value });
        simp();
    }
}
```

```expect
pass
```
