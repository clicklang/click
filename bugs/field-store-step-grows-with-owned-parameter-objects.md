# A field store's step grows with the owned parameter objects

A simple `step` over a store must cost work proportional to the store
(docs/internals/verification-efficiency.md). Storing to one field of one owned
parameter object costs work linear in how many other owned parameter objects
the function holds, so initializing N objects is quadratic.

Reproduced on master `0d2b58555` with `scripts/step-scaling-hunt.py`, which
generates the C below with an explicit one-`step()`-per-statement proof:

```c
int32 caller(int32* flags, int32* data, int32 k, struct box* b0, ..., struct box* bN) {
    int32 total;
    b0->v = 0; ... bN->v = N;          /* each store step measured */
    touch(flags, data, k);
    total = b0->v + ... + bN->v;
    return total;
}
```

```sh
python3 scripts/step-scaling-hunt.py many_objects deep_chain --sizes 1,8,32,64
```

Each `bi->v = i` step charges 63, 194, 554 and 1,034 units at N = 1, 8, 32
and 64. A pointer-valued store (`ni->next = n(i+1)`, shape `deep_chain`) grows
faster: about 5,354 units at N = 32 and 10,410 at 64. All parameters share the
`ExternalArgument` block, so an index by block does not separate them. A
profile at N = 256 shows every statement also collecting the variables of the
whole state and fact set (`statement_kernel_variables`), work that is not
charged; the charged growth is in the store's own execution and was not yet
isolated.

Acceptance: a multi-size regression over the `many_objects` and `deep_chain`
shapes shows each store step's work, and its time, constant in N up to
logarithmic factors; ownership and write permission are still checked per
store; no budget or threshold is raised.
