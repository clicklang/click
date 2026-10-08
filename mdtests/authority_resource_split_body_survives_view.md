# Split ordinary bodies remain canonical across opaque views in authority mode

An opaque mutation inside `open(wrapper(pair))` may split the object body into
field ranges. A later call that views `wrapper(pair)` must recognize those
ranges as the one body of the folded wrapper, rather than trying to compose a
duplicate whole object.

This is the authority form of
`resource_population_split_body_survives_view.md`. Under legacy semantics,
`wrapper` was a counted population whose body stayed exposed, so the
pipeline returned `owns *pair` without unfolding. Under authority semantics
`wrapper` is an ordinary family. The pipeline holds the folded
`wrapper(pair)` that `wrap_pair` produced and unfolds it to return the
object.

```c filename=resource_population_split_wrap.c
struct pair {
    int32 left;
    int32 right;
};

void wrap_pair(struct pair* pair) {
}
```

```c filename=resource_population_split_set.c
struct pair {
    int32 left;
    int32 right;
};

void set_left(struct pair* pair) {
    pair->left = 7;
}
```

```c filename=resource_population_split_read.c
struct pair {
    int32 left;
    int32 right;
};

int32 read_right(struct pair* pair) {
    return pair->right;
}
```

```c filename=resource_population_split_pipeline.c
struct pair {
    int32 left;
    int32 right;
};

void split_body_pipeline(struct pair* pair) {
    wrap_pair(pair);
    set_left(pair);
    read_right(pair);
}
```

```click resource_semantics=authority
resource wrapper(pair: struct pair*) {
    owns *pair;
}

verifying "resource_population_split_wrap.c";
verifying "resource_population_split_set.c";
verifying "resource_population_split_read.c";
verifying "resource_population_split_pipeline.c";

void wrap_pair(struct pair* pair) {
    consumes *pair;
    produces wrapper(pair);
} by {
    execute();
    fold(wrapper(pair));
    simp();
}

void set_left(struct pair* pair) {
    owns wrapper(pair);
} by {
    open(wrapper(pair)) {
        execute();
        simp();
    }
}

int32 read_right(struct pair* pair) {
    views wrapper(pair);

    ensures result == pair->right by auto;
}

void split_body_pipeline(struct pair* pair) {
    owns *pair;
} by {
    execute();
    unfold(wrapper(pair));
    simp();
}
```

```expect
pass
```
