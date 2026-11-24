# Explicit Boolean and constructor conditional equations

A Boolean conditional follows its selected arm's truth. A constructor equation
can rewrite a conditional inside a constructor field.

```click
spec enum Choice { Missing, Present(int32), }
spec enum Wrapper { Wrap(Choice), }

theorem selected_truth(flag: Bool, value: Bool) {
    requires flag;
    requires value;
    ensures (if flag { value } else { false }) == true by close();
}

theorem selected_field(flag: Bool, value: int32) {
    requires flag;
    ensures Wrapper::Wrap(if flag { Choice::Present(value) } else { Choice::Missing })
        == Wrapper::Wrap(Choice::Present(value)) by {
        have (if flag { Choice::Present(value) } else { Choice::Missing })
            == Choice::Present(value) by close();
        rewrite((if flag { Choice::Present(value) } else { Choice::Missing }),
            Choice::Present(value));
        close();
    }
}
```

```expect
pass
```
