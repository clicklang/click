# `instantiate` on an `Integer` or pointer binder misreports the argument

Soundness: not soundness. These steps are outside `instantiate`'s supported
binder types and are correctly refused. The defect is the message: it blames
the argument, which is a valid expression of the binder's type, instead of
saying the binder type is unsupported.

The violated invariant: a refusal names the actual reason. [Universal
instantiation](../docs/reference/tactics/index.md#universal-instantiation)
accepts `int32` and `uint64` binders and says an `Integer` or pointer binder
is "not supported by `instantiate`", with the workaround of stating the
instance as a theorem and applying it. It also records the current message,
"argument did not evaluate to int32", which is false for the literal `5` and
says nothing about binder types. With an `Integer` argument written through
`to_integer`, the message is instead "unknown function `to_integer`", a
function every Click program can use.

```c filename=z.c
void unused() {}
```

```click
verifying "z.c";

theorem t(x: int32) {
    requires forall (z: Integer) { z + 0 == z };
    ensures 5 + 0 == 5 by {
        instantiate(forall (z: Integer) { z + 0 == z }, 5);
    }
}
```

`click verify` prints:

```text
proof error:
  `instantiate` argument did not evaluate to int32

tactic@6:
  instantiate(forall (z: Integer) { z + 0 == z }, 5);
goal: true
refused by: `instantiate` (simple: a refusal within its documented behavior is a bug)
see: click docs instantiate
```

With the argument `to_integer(x)` (goal `to_integer(x) + 0 == to_integer(x)`):

```text
proof error:
  could not evaluate `instantiate` argument
  unknown function `to_integer`
```

With a pointer binder:

```click
verifying "z.c";

theorem t(q: int32*) {
    requires forall (p: int32*) { p == p };
    ensures q == q by {
        instantiate(forall (p: int32*) { p == p }, q);
    }
}
```

```text
proof error:
  `instantiate` argument did not evaluate to int32
```

## Acceptance criteria

- All three reproductions are refused with a message saying `instantiate`
  does not support an `Integer` (respectively pointer) binder, naming the
  binder and its type, and pointing to the theorem-and-`apply` workaround.
  The message does not mention evaluating the argument or `to_integer`.
- The check runs on the binder type before the argument is evaluated, so the
  argument's spelling does not change the message.
- The reference's "Outside it" entry quotes the new message.
- A regression covers the `Integer` binder with a literal argument and with a
  `to_integer(...)` argument, and the pointer binder.
