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
            apply(separation::subrange(p, lo, hi, i, i + 1)) using {
                defined(i + 1); lo <= i; i <= ((i + 1) as int32); ((i + 1) as int32) <= hi;
            };
        }
        have separate(kept, memory(p[i..i + 1])) by {
            apply(separation::restrict(whole, memory(p[lo..hi]), kept, memory(p[i..i + 1]))) using {
                defined(i + 1); separate(whole, memory(p[lo..hi])); contains(whole, kept);
                contains(memory(p[lo..hi]), memory(p[i..i + 1]));
            };
        }
        have contains(kept, kept) by { normalize(); }
        have contains(memory(p[i..i + 1]), memory(p[i])) by { normalize(); }
        apply(separation::restrict(kept, memory(p[i..i + 1]), kept, memory(p[i]))) using {
            defined(i + 1); separate(kept, memory(p[i..i + 1])); contains(kept, kept);
            contains(memory(p[i..i + 1]), memory(p[i]));
        };
    }
}

verifying "fork_join.c";

predicate range_filled(job: struct range_job*) {
    forall (k: int32) {
        job->begin <= k and k < job->end implies job->output[k] == job->value
    }
}

resource filled_range(output: int*, begin: int32, end: int32, value: int32) {
    owns output[begin..end];
    fact forall (k: int32) { begin <= k and k < end implies output[k] == value };
}

void *fill_range(void *argument) {
    views (argument as (struct range_job *))->output;
    views (argument as (struct range_job *))->begin;
    views (argument as (struct range_job *))->end;
    views (argument as (struct range_job *))->value;
    consumes (argument as (struct range_job *))->output[(argument as (struct range_job *))->begin..(argument as (struct range_job *))->end];
    requires 0 <= (argument as (struct range_job *))->begin;
    requires (argument as (struct range_job *))->begin <= (argument as (struct range_job *))->end;
    requires 0 <= (argument as (struct range_job *))->end - (argument as (struct range_job *))->begin;
    requires (argument as (struct range_job *))->end - (argument as (struct range_job *))->begin <= 1073741823;
    requires separate(memory(*(argument as (struct range_job *))), memory((argument as (struct range_job *))->output[(argument as (struct range_job *))->begin..(argument as (struct range_job *))->end]));
    produces filled_range(
        (argument as (struct range_job *))->output,
        (argument as (struct range_job *))->begin,
        (argument as (struct range_job *))->end,
        (argument as (struct range_job *))->value
    );
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
            have job->begin <= index and index <= job->end;
            have forall (k: int32) { job->begin <= k and k < index implies job->output[k] == job->value } by {
                intro();
                intro();
                contradiction(job->begin <= k and k < index);
            }
        }
        preserve by {
            have separate(memory(*job), memory(job->output[job->begin..job->end]));
            have job->begin <= index;
            have contains(memory(*job), memory(job->output)) by { normalize(); }
            have separate(memory(job->output[index]), memory(job->output)) by {
                apply(selected_array_cell(memory(*job), memory(job->output), job->output, job->begin, job->end, index)) using {
                    separate(memory(*job), memory(job->output[job->begin..job->end]));
                    contains(memory(*job), memory(job->output));
                    0 <= job->begin; job->begin <= index; index < job->end;
                };
                apply(separation::separate_symm(memory(job->output), memory(job->output[index]))) using {
                    separate(memory(job->output), memory(job->output[index]));
                };
            }
            have contains(memory(*job), memory(job->begin)) by { normalize(); }
            have separate(memory(job->output[index]), memory(job->begin)) by {
                apply(selected_array_cell(memory(*job), memory(job->begin), job->output, job->begin, job->end, index)) using {
                    separate(memory(*job), memory(job->output[job->begin..job->end]));
                    contains(memory(*job), memory(job->begin));
                    0 <= job->begin; job->begin <= index; index < job->end;
                };
                apply(separation::separate_symm(memory(job->begin), memory(job->output[index]))) using {
                    separate(memory(job->begin), memory(job->output[index]));
                };
            }
            have contains(memory(*job), memory(job->end)) by { normalize(); }
            have separate(memory(job->output[index]), memory(job->end)) by {
                apply(selected_array_cell(memory(*job), memory(job->end), job->output, job->begin, job->end, index)) using {
                    separate(memory(*job), memory(job->output[job->begin..job->end]));
                    contains(memory(*job), memory(job->end));
                    0 <= job->begin; job->begin <= index; index < job->end;
                };
                apply(separation::separate_symm(memory(job->end), memory(job->output[index]))) using {
                    separate(memory(job->end), memory(job->output[index]));
                };
            }
            have contains(memory(*job), memory(job->value)) by { normalize(); }
            have separate(memory(job->output[index]), memory(job->value)) by {
                apply(selected_array_cell(memory(*job), memory(job->value), job->output, job->begin, job->end, index)) using {
                    separate(memory(*job), memory(job->output[job->begin..job->end]));
                    contains(memory(*job), memory(job->value));
                    0 <= job->begin; job->begin <= index; index < job->end;
                };
                apply(separation::separate_symm(memory(job->value), memory(job->output[index]))) using {
                    separate(memory(job->value), memory(job->output[index]));
                };
            }
            have contains(memory(job->output[job->begin..job->end]), memory(job->output[index])) by {
                apply(separation::contains_element(job->output, job->begin, job->end, index)) using { job->begin <= index; index < job->end; };
            }
            have separate(memory(job->output[index]), memory(*job)) by { solve(); }
            mark iteration;
            step();
            have at(iteration, separate(loop(0).statement(0).footprint, memory(job->output))) by { normalize() using {
                at(iteration, separate(memory(job->output[index]), memory(job->output)));
            }; }
            have job->output == at(iteration, job->output) by {
                transport_certificate {
                    premise 0: at(iteration, separate(loop(0).statement(0).footprint, memory(job->output))) => at(iteration, separate(loop(0).statement(0).footprint, memory(job->output)));
                    preserve 0 => job->output == at(iteration, job->output);
                    conclusion 1;
                }
            }
            have at(iteration, separate(loop(0).statement(0).footprint, memory(job->begin))) by { normalize() using {
                at(iteration, separate(memory(job->output[index]), memory(job->begin)));
            }; }
            have job->begin == at(iteration, job->begin) by {
                transport_certificate {
                    premise 0: at(iteration, separate(loop(0).statement(0).footprint, memory(job->begin))) => at(iteration, separate(loop(0).statement(0).footprint, memory(job->begin)));
                    preserve 0 => job->begin == at(iteration, job->begin);
                    conclusion 1;
                }
            }
            have at(iteration, separate(loop(0).statement(0).footprint, memory(job->end))) by { normalize() using {
                at(iteration, separate(memory(job->output[index]), memory(job->end)));
            }; }
            have job->end == at(iteration, job->end) by {
                transport_certificate {
                    premise 0: at(iteration, separate(loop(0).statement(0).footprint, memory(job->end))) => at(iteration, separate(loop(0).statement(0).footprint, memory(job->end)));
                    preserve 0 => job->end == at(iteration, job->end);
                    conclusion 1;
                }
            }
            have at(iteration, separate(loop(0).statement(0).footprint, memory(job->value))) by { normalize() using {
                at(iteration, separate(memory(job->output[index]), memory(job->value)));
            }; }
            have job->value == at(iteration, job->value) by { assumption(); }
            have forall (k: int32) {
                job->begin <= k and k <= index implies job->output[k] == job->value
            } by {
                intro();
                intro();
                if k < index {
                    extract(job->begin <= k);
                    instantiate(at(region(5).entry, forall (k: int32) {
                        job->begin <= k and k < index implies job->output[k] == job->value
                    }), k) using { job->begin <= k; k < index; job->begin == at(iteration, job->begin); };
                    solve();
                } else {
                    extract(k <= index);
                    have k == index;
                    rewrite(k == index);
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
                extract(job->begin <= k);
                extract(k < index);
                have k <= at(iteration, index);
                instantiate(at(region(6).entry, forall (k: int32) {
                    job->begin <= k and k <= index implies job->output[k] == job->value
                }), k) using { job->begin <= k; k <= at(iteration, index); job->begin == at(iteration, job->begin); };
                solve();
            }
            solve();
        }
    }
    step();
    fold(filled_range((argument as (struct range_job *))->output, (argument as (struct range_job *))->begin, (argument as (struct range_job *))->end, (argument as (struct range_job *))->value));
    solve();
}

int fill_parallel(int output[4]) {
    owns output[0..4];
    ensures result == 0 or result == 1;
    ensures result == 1 implies
        output[0] == 11 and output[1] == 11 and
        output[2] == 22 and output[3] == 22;
    ensures result == 0 implies
        (output[0] == 0 and output[1] == 0 and
         output[2] == 0 and output[3] == 0) or
        (output[0] == 11 and output[1] == 11 and
         output[2] == 0 and output[3] == 0);
} by {
    step_until(statement(5));
    have first_job.output == output;
    have second_job.output == output;
    step();
    branch {
        step_until(function.exit);
        solve();
    } else {}
    step();
    branch {
        step();
        have first_job.output == output;
        have first_job.begin == 0;
        have first_job.end == 2;
        have first_job.value == 11;
        unfold(filled_range(output, 0, 2, 11));
        // Select the returned range at this index before rewriting the job fields.
        have forall (k: int32) {
            first_job.begin <= k and k < first_job.end implies first_job.output[k] == first_job.value
        } by {
            intro() as k;
            intro();
            have 0 <= k by { rewrite(0 == first_job.begin); assumption(); }
            have k < 2 by { rewrite(2 == first_job.end); assumption(); }
            instantiate(forall (j: int32) { 0 <= j and j < 2 implies output[j] == 11 }, k) using {
                0 <= k; k < 2;
            };
            rewrite(first_job.output == output);
            rewrite(first_job.value == 11);
            assumption();
        }
        have range_filled(&first_job) by { unfold(range_filled); assumption(); }
        have first_job.output[0] == first_job.value;
        have first_job.output[1] == first_job.value;
        have output[0] == 11;
        have output[1] == 11;
        step_until(function.exit);
        solve();
    } else {}
    step();
    have first_job.output == output;
    have first_job.begin == 0;
    have first_job.end == 2;
    have first_job.value == 11;
    unfold(filled_range(output, 0, 2, 11));
    // Select the returned range at this index before rewriting the job fields.
    have forall (k: int32) {
        first_job.begin <= k and k < first_job.end implies first_job.output[k] == first_job.value
    } by {
        intro() as k;
        intro();
        have 0 <= k by { rewrite(0 == first_job.begin); assumption(); }
        have k < 2 by { rewrite(2 == first_job.end); assumption(); }
        instantiate(forall (j: int32) { 0 <= j and j < 2 implies output[j] == 11 }, k) using {
            0 <= k; k < 2;
        };
        rewrite(first_job.output == output);
        rewrite(first_job.value == 11);
        assumption();
    }
    have range_filled(&first_job) by { unfold(range_filled); assumption(); }
    have first_job.output[0] == first_job.value;
    have first_job.output[1] == first_job.value;
    have output[0] == 11;
    have output[1] == 11;
    step();
    unfold(filled_range(output, 2, 4, 22));
    have range_filled(&second_job);
    have forall (k: int32) {
        second_job.begin <= k and k < second_job.end implies second_job.output[k] == second_job.value
    } by { unfold(range_filled); assumption(); }
    have second_job.output[2] == second_job.value;
    have second_job.output[3] == second_job.value;
    have output[2] == 22;
    have output[3] == 22;
    step_until(function.exit);
    solve();
}
