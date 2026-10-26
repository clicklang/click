# The frozen worker verifies with direct borrowed and owned clauses

The C worker is unchanged from `examples/concurrency-fork-join/fork_join.c`.
Direct `views` clauses allow a future caller to lend its job record while
transferring the output slice. Certificate synthesis must spell the output
pointer through the cast `void *` parameter or the struct-pointer local,
including when checking an expanded quantified readability proof.

```c filename=fill_range.c
#include <stddef.h>

struct range_job {
    int *output;
    int begin;
    int end;
    int value;
};

void *fill_range(void *argument) {
    struct range_job *job = argument;
    for (int index = job->begin; index < job->end; ++index) {
        job->output[index] = job->value;
    }
    return NULL;
}
```

```click
target "x86_64-unknown-linux-gnu";
verifying "fill_range.c";

predicate range_filled(job: struct range_job*) {
    forall (k: int32) {
        job->begin <= k and k < job->end implies job->output[k] == job->value
    }
}

void *fill_range(void *argument) {
    views (argument as (struct range_job *))->output;
    views (argument as (struct range_job *))->begin;
    views (argument as (struct range_job *))->end;
    views (argument as (struct range_job *))->value;
    owns (argument as (struct range_job *))->output[(argument as (struct range_job *))->begin..(argument as (struct range_job *))->end];
    requires 0 <= (argument as (struct range_job *))->begin;
    requires (argument as (struct range_job *))->begin <= (argument as (struct range_job *))->end;
    requires 0 <= to_integer((argument as (struct range_job *))->end - (argument as (struct range_job *))->begin);
    requires to_integer((argument as (struct range_job *))->end - (argument as (struct range_job *))->begin) <= 1073741823;
    requires separate(memory(*(argument as (struct range_job *))), memory((argument as (struct range_job *))->output[(argument as (struct range_job *))->begin..(argument as (struct range_job *))->end]));
    ensures result == 0;
    ensures range_filled(argument as (struct range_job *));
} by {
    step();
    step();
    step();
    step();
    loop as fill {
        decreases job->end - index;
        views job->output;
        views job->begin;
        views job->end;
        views job->value;
        owns job->output[job->begin..job->end];
        invariant job->begin <= index and index <= job->end;
        invariant forall (k: int32) {
            job->begin <= k and k < index implies job->output[k] == job->value
        };

        initialize by {
            have job->begin <= index and index <= job->end by {
                both { normalize(); } and { assumption(); }
            }
            have forall (k: int32) { job->begin <= k and k < index implies job->output[k] == job->value } by {
                intro();
                intro();
                contradiction(job->begin <= k and k < index);
            }
        }
        preserve by {
            mark iteration;
            step();
            step();
            have 0 <= at(iteration, index) by {
                solve() using {
                    0 <= job->begin;
                    job->begin <= at(iteration, index);
                };
            }
            have 0 <= job->end by {
                solve() using {
                    0 <= job->begin;
                    job->begin <= job->end;
                };
            }
            have 0 <= to_integer(0 - at(iteration, index) + job->end - 1) by {
                solve() using {
                    0 <= at(iteration, index);
                    0 <= job->end;
                    at(iteration, index) < at(iteration, job->end);
                    job->begin <= job->end;
                };
            }
            have to_integer(0 - at(iteration, index) + job->end - 1)
                < to_integer(0 - at(iteration, index) + job->end) by {
                solve() using {
                    0 <= at(iteration, index);
                    0 <= job->end;
                    at(iteration, index) < at(iteration, job->end);
                    job->begin <= job->end;
                };
            }
            solve();
        }
    }
    step();
    solve();
}
```

```expect
pass
```
