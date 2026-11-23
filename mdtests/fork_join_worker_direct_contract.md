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

import click::separation;

theorem selected_array_cell(whole: Resource, kept: Resource, p: int32*, lo: int32, hi: int32, i: int32) {
    requires separate(whole, memory(p[lo..hi]));
    requires contains(whole, kept);
    requires 0 <= lo;
    requires lo <= i;
    requires i < hi;
    ensures separate(kept, memory(p[i])) by {
        have 0 <= i by { solve() using { 0 <= lo; lo <= i; }; }
        have i <= 2147483646 by { solve() using { i < hi; }; }
        have defined(i + 1) by { solve() using { 0 <= i; i <= 2147483646; }; }
        have i <= ((i + 1) as int32) by { solve() using { 0 <= i; i < hi; }; }
        have ((i + 1) as int32) <= hi by { solve() using { 0 <= i; i < hi; }; }
        have contains(memory(p[lo..hi]), memory(p[i..i + 1])) by {
            apply(separation::contains_subrange(p, lo, hi, i, i + 1));
        }
        have separate(kept, memory(p[i..i + 1])) by {
            apply(separation::separate_restrict(whole, memory(p[lo..hi]), kept, memory(p[i..i + 1])));
        }
        have contains(kept, kept) by { apply(click::separation::contains_refl(kept)); }
        have contains(memory(p[i..i + 1]), memory(p[i])) by { normalize(); }
        apply(separation::separate_restrict(kept, memory(p[i..i + 1]), kept, memory(p[i])));
    }
}

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
    loop fill {
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
                all { job->begin <= index => { normalize(); } index <= job->end => { known(); } }
            }
            have forall (k: int32) { job->begin <= k and k < index implies job->output[k] == job->value } by {
                intro();
                intro();
                contradiction(job->begin <= k and k < index);
            }
        }
        maintain by {
            have separate(memory(*job), memory(job->output[job->begin..job->end]));
            have job->begin <= index;
            have contains(memory(*job), memory(job->output)) by { normalize(); }
            have separate(memory(job->output[index]), memory(job->output)) by {
                apply(selected_array_cell(memory(*job), memory(job->output), job->output, job->begin, job->end, index));
                apply(separation::separate_symm(memory(job->output), memory(job->output[index])));
            }
            have contains(memory(*job), memory(job->begin)) by { normalize(); }
            have separate(memory(job->output[index]), memory(job->begin)) by {
                apply(selected_array_cell(memory(*job), memory(job->begin), job->output, job->begin, job->end, index));
                apply(separation::separate_symm(memory(job->begin), memory(job->output[index])));
            }
            have contains(memory(*job), memory(job->end)) by { normalize(); }
            have separate(memory(job->output[index]), memory(job->end)) by {
                apply(selected_array_cell(memory(*job), memory(job->end), job->output, job->begin, job->end, index));
                apply(separation::separate_symm(memory(job->end), memory(job->output[index])));
            }
            have contains(memory(*job), memory(job->value)) by { normalize(); }
            have separate(memory(job->output[index]), memory(job->value)) by {
                apply(selected_array_cell(memory(*job), memory(job->value), job->output, job->begin, job->end, index));
                apply(separation::separate_symm(memory(job->value), memory(job->output[index])));
            }
            have contains(memory(job->output[job->begin..job->end]), memory(job->output[index])) by {
                apply(separation::contains_element(job->output, job->begin, job->end, index));
            }
            have separate(memory(job->output[index]), memory(*job)) by { solve(); }
            mark iteration;
            step();
            have at(iteration, separate(loop(0).statement(0).footprint, memory(job->output))) by { known(); }
            have job->output == at(iteration, job->output) by {
                preserve(at(iteration, memory(job->output)), loop(0).statement(0));
            }
            have at(iteration, separate(loop(0).statement(0).footprint, memory(job->begin))) by { known(); }
            have job->begin == at(iteration, job->begin) by {
                preserve(at(iteration, memory(job->begin)), loop(0).statement(0));
            }
            have at(iteration, separate(loop(0).statement(0).footprint, memory(job->end))) by { known(); }
            have job->end == at(iteration, job->end) by {
                preserve(at(iteration, memory(job->end)), loop(0).statement(0));
            }
            have at(iteration, separate(loop(0).statement(0).footprint, memory(job->value))) by { known(); }
            have job->value == at(iteration, job->value) by { known(); }
            have forall (k: int32) {
                job->begin <= k and k <= index implies job->output[k] == job->value
            } by {
                intro();
                intro();
                if k < index {
                    have job->begin <= k;
                    instantiate(at(region(5).entry, forall (k: int32) {
                        job->begin <= k and k < index implies job->output[k] == job->value
                    }), k);
                    have at(iteration, job->output[k]) == at(iteration, job->value) by { known(); }
                    // The write at index preserves the earlier cell at k.
                    have k != index;
                    have at(iteration, separate(memory(job->output[index]), memory(job->output[k]))) by {
                        apply(separation::separate_elements(at(iteration, job->output), at(iteration, index), k));
                    }
                    have contains(at(iteration, memory(job->output[k])), at(iteration, memory((&job->output[k])[0..1]))) by { normalize(); }
                    apply(separation::contains_refl(at(iteration, memory(job->output[index]))));
                    have separate(at(iteration, memory(job->output[index])), at(iteration, memory((&job->output[k])[0..1]))) by {
                        apply(separation::separate_restrict(at(iteration, memory(job->output[index])), at(iteration, memory(job->output[k])), at(iteration, memory(job->output[index])), at(iteration, memory((&job->output[k])[0..1]))));
                    }
                    have separate(loop(0).statement(0).footprint, at(iteration, memory((&job->output[k])[0..1]))) by {
                        known();
                    }
                    have at(loop(0).statement(0).exit, load<int32>(at(iteration, &job->output[k])))
                        == at(loop(0).statement(0).entry, load<int32>(at(iteration, &job->output[k]))) by {
                        preserve(at(iteration, memory((&job->output[k])[0..1])), loop(0).statement(0));
                    }
                    rewrite(job->output, at(iteration, job->output));
                    known();
                } else {
                    have k <= index;
                    have k == index;
                    rewrite(k, index);
                    solve();
                }
            }
            step();
            have 0 <= at(iteration, index);
            have 0 <= job->end;
            have 0 - at(iteration, index) + job->end - 1
                < 0 - at(iteration, index) + job->end by {
                solve() using {
                    0 <= at(iteration, index);
                    0 <= job->end;
                    at(iteration, index) < at(iteration, job->end);
                    job->begin <= job->end;
                };
            }
            have forall (k: int32) {
                job->begin <= k and k < index implies job->output[k] == job->value
            } by {
                intro();
                intro();
                have job->begin <= k;
                have k < index;
                have k <= at(iteration, index);
                have job->begin <= k and k <= index;
                instantiate(at(region(6).entry, forall (k: int32) {
                    job->begin <= k and k <= index implies job->output[k] == job->value
                }), k);
                solve();
            }
            solve();
        }
        otherwise {
            have index == job->end by solve();
            have forall (k: int32) {
                job->begin <= k and k < job->end implies job->output[k] == job->value
            } by {
                intro();
                intro();
                have job->begin <= k and k < index by solve();
                instantiate(forall (k: int32) {
                    job->begin <= k and k < index implies job->output[k] == job->value
                }, k);
                solve();
            }
        }
    }
    step();
    solve();
}
```

```expect
pass
```
