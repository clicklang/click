import click::integer;
import click::separation;

theorem selected_array_cell(whole: Resource, kept: Resource, p: int32*, lo: int32, hi: int32, i: int32) {
    requires separate(whole, memory(p[lo..hi]));
    requires contains(whole, kept);
    requires 0 <= lo;
    requires lo <= i;
    requires i < hi;
    ensures separate(kept, memory(p[i])) by {
        have contains(memory(p[lo..hi]), memory(p[i])) by {
            apply(separation::contains_element(p, lo, hi, i));
        }
        apply(separation::separate_restrict(whole, memory(p[lo..hi]), kept, memory(p[i])));
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
    loop fill {
        decreases to_integer(job->end) - to_integer(index);
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
                intro() {
                    intro() {
                        contradiction(job->begin <= k and k < index);
                    }
                }
            }
        }
        maintain by {
            // The output store leaves the range descriptor and earlier cells intact.
            mark before_write;
            have separate(memory(*job), memory(job->output[job->begin..job->end])) by { close(); }
            have contains(memory(job->output[job->begin..job->end]), memory(job->output[index])) by {
                apply(separation::contains_element(job->output, job->begin, job->end, index));
            }
            apply(separation::contains_refl(memory(*job)));
            apply(separation::separate_restrict(memory(*job), memory(job->output[job->begin..job->end]),
                memory(*job), memory(job->output[index])));
            step() by { close(); }

            have separate(loop(0).statement(0).footprint, at(before_write, memory(*job))) by {
                close() using {
                    separate(at(before_write, memory(job->output[index])), at(before_write, memory(*job)));
                };
            }
            apply(separation::contains_refl(loop(0).statement(0).footprint));
            have contains(at(before_write, memory(*job)), at(before_write, memory(job->begin))) by { close(); }
            apply(separation::separate_restrict(loop(0).statement(0).footprint, at(before_write, memory(*job)),
                loop(0).statement(0).footprint, at(before_write, memory(job->begin))));
            have job->begin == at(before_write, job->begin) by {
                preserve(at(before_write, memory(job->begin)), loop(0).statement(0));
            }
            have contains(at(before_write, memory(*job)), at(before_write, memory(job->output))) by { close(); }
            apply(separation::separate_restrict(loop(0).statement(0).footprint, at(before_write, memory(*job)),
                loop(0).statement(0).footprint, at(before_write, memory(job->output))));
            have job->output == at(before_write, job->output) by {
                preserve(at(before_write, memory(job->output)), loop(0).statement(0));
            }
            have contains(at(before_write, memory(*job)), at(before_write, memory(job->end))) by { close(); }
            apply(separation::separate_restrict(loop(0).statement(0).footprint, at(before_write, memory(*job)),
                loop(0).statement(0).footprint, at(before_write, memory(job->end))));
            have job->end == at(before_write, job->end) by {
                preserve(at(before_write, memory(job->end)), loop(0).statement(0));
            }
            have contains(at(before_write, memory(*job)), memory(at(before_write, &job->value)[0])) by { close(); }
            apply(separation::separate_restrict(loop(0).statement(0).footprint, at(before_write, memory(*job)),
                loop(0).statement(0).footprint, memory(at(before_write, &job->value)[0])));
            have load<int32>(at(before_write, &job->value)) == at(before_write, load<int32>(&job->value)) by {
                preserve(memory(at(before_write, &job->value)[0]), loop(0).statement(0));
            }
            have job->value == at(before_write, job->value) by { close(); }

            have forall (k: int32) { job->begin <= k and k <= index implies job->output[k] == job->value } by {
                intro() {
                    intro() {
                        if k < index {
                            instantiate(at(before_write, forall (k: int32) {
                                job->begin <= k and k < index implies job->output[k] == job->value
                            }), k);
                            have at(before_write, job->begin) <= k and k < at(before_write, index) by {
                                rewrite(at(before_write, job->begin), job->begin);
                                close();
                            }
                            apply(at(before_write, job->begin) <= k and k < at(before_write, index) implies
                                at(before_write, job->output[k]) == at(before_write, job->value));
                            have k != at(before_write, index) by { close() using { k < index; }; }
                            have separate(at(before_write, memory(job->output[k])), at(before_write, memory(job->output[index]))) by {
                                apply(separation::separate_elements(at(before_write, job->output), k, at(before_write, index)));
                            }
                            have separate(loop(0).statement(0).footprint, at(before_write, memory(job->output[k]))) by {
                                apply(separation::separate_symm(at(before_write, memory(job->output[k])),
                                    at(before_write, memory(job->output[index]))));
                                close() using {
                                    separate(at(before_write, memory(job->output[index])), at(before_write, memory(job->output[k])));
                                };
                            }
                            have load<int32>(at(before_write, &job->output[k])) == at(before_write, job->output[k]) by {
                                preserve(at(before_write, memory(job->output[k])), loop(0).statement(0));
                            }
                            rewrite(job->output, at(before_write, job->output));
                            rewrite(job->value, at(before_write, job->value));
                            close();
                        } else {
                            have k == index;
                            rewrite(k, index);
                            close();
                        }
                    }
                }
            }

            // The increment moves the inclusive prefix back to the loop invariant.
            mark after_write;
            step();
            have at(before_write, index) < job->end by {
                rewrite(job->end, at(before_write, job->end));
                close();
            }
            have at(after_write, index) < 2147483647 by {
                apply(integer::int32_less_than_less_equal_transitive(at(after_write, index), job->end, 2147483647));
            }
            apply(integer::int32_increment_below_max_is_defined(at(after_write, index)));
            have to_integer(index) == to_integer(at(before_write, index)) + 1 by {
                have to_integer(index) == to_integer(at(after_write, index) + 1) by { close(); }
                apply(integer::int32_add_to_integer(at(after_write, index), 1));
                close();
            }
            have forall (k: int32) { job->begin <= k and k < index implies job->output[k] == job->value } by {
                intro() {
                    intro() {
                        have k <= at(after_write, index) by {
                            have to_integer(k) < to_integer(index) by { close(); }
                            apply(integer::lt_le_predecessor(to_integer(k), to_integer(index)));
                            have to_integer(at(after_write, index)) == to_integer(index) - 1 by {
                                rewrite(to_integer(index), to_integer(at(before_write, index)) + 1);
                                close();
                            }
                            have to_integer(k) <= to_integer(at(after_write, index)) by {
                                rewrite(to_integer(at(after_write, index)), to_integer(index) - 1);
                                close();
                            }
                            apply(integer::int32_to_integer_less_equal_implies_less_equal(k, at(after_write, index)));
                        }
                        instantiate(at(after_write, forall (k: int32) {
                            job->begin <= k and k <= index implies job->output[k] == job->value
                        }), k);
                        have at(after_write, job->begin) <= k and k <= at(after_write, index) by { close(); }
                        apply(at(after_write, job->begin) <= k and k <= at(after_write, index) implies
                            at(after_write, job->output[k]) == at(after_write, job->value));
                        close();
                    }
                }
            }
            have job->begin <= index by {
                have at(after_write, job->begin) <= at(after_write, index) by { close(); }
                apply(integer::int32_increment_lower_bound(at(after_write, index), at(after_write, job->begin), job->end));
                have to_integer(job->begin) <= to_integer(index) by { close(); }
                apply(integer::int32_to_integer_less_equal_implies_less_equal(job->begin, index));
            }
            have index <= job->end by {
                apply(integer::int32_increment_upper_bound(at(after_write, index), job->end));
                have to_integer(index) <= to_integer(job->end) by { close(); }
                apply(integer::int32_to_integer_less_equal_implies_less_equal(index, job->end));
            }
            have 0 <= to_integer(job->end) - to_integer(index) by {
                close() using { index <= job->end; };
            }
            have to_integer(job->end) - to_integer(index) < at(before_write, to_integer(job->end) - to_integer(index)) by {
                rewrite(to_integer(index), to_integer(at(before_write, index)) + 1);
                rewrite(at(before_write, job->end), job->end);
                close();
            }
            close();
        }
        otherwise {
            have index == job->end by close();
            have forall (k: int32) {
                job->begin <= k and k < job->end implies job->output[k] == job->value
            } by {
                intro() {
                    intro() {
                        have job->begin <= k and k < index by close();
                        instantiate(forall (k: int32) {
                            job->begin <= k and k < index implies job->output[k] == job->value
                        }, k);
                        close();
                    }
                }
            }
        }
    }
    step();
    fold(filled_range((argument as (struct range_job *))->output, (argument as (struct range_job *))->begin, (argument as (struct range_job *))->end, (argument as (struct range_job *))->value));
    close();
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
    step_until(statement(5).entry);
    have first_job.output == output;
    have second_job.output == output;
    step();
    branch {
        true => {
            step_until(function.exit);
            close();
        }
        false => {}
    }
    step();
    branch {
        true => {
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
                intro(k) {
                    intro() {
                        have 0 <= k by { rewrite(0, first_job.begin); close(); }
                        have k < 2 by { rewrite(2, first_job.end); close(); }
                        instantiate(forall (j: int32) { 0 <= j and j < 2 implies output[j] == 11 }, k);
                        rewrite(first_job.output, output);
                        rewrite(first_job.value, 11);
                        close();
                    }
                }
            }
            have first_job.output[0] == first_job.value by {
                have first_job.begin <= 0 and 0 < first_job.end;
                instantiate(forall (j: int32) { first_job.begin <= j and j < first_job.end implies first_job.output[j] == first_job.value }, 0);
                close();
            }
            have first_job.output[1] == first_job.value by {
                have first_job.begin <= 1 and 1 < first_job.end;
                instantiate(forall (j: int32) { first_job.begin <= j and j < first_job.end implies first_job.output[j] == first_job.value }, 1);
                close();
            }
            have output[0] == 11;
            have output[1] == 11 by {
                instantiate(forall (j: int32) { 0 <= j and j < 2 implies output[j] == 11 }, 1);
                close();
            }
            step_until(function.exit);
            close();
        }
        false => {}
    }
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
        intro(k) {
            intro() {
                have 0 <= k by { rewrite(0, first_job.begin); close(); }
                have k < 2 by { rewrite(2, first_job.end); close(); }
                instantiate(forall (j: int32) { 0 <= j and j < 2 implies output[j] == 11 }, k);
                rewrite(first_job.output, output);
                rewrite(first_job.value, 11);
                close();
            }
        }
    }
    have first_job.output[0] == first_job.value by {
        have first_job.begin <= 0 and 0 < first_job.end;
        instantiate(forall (j: int32) { first_job.begin <= j and j < first_job.end implies first_job.output[j] == first_job.value }, 0);
        close();
    }
    have first_job.output[1] == first_job.value by {
        have first_job.begin <= 1 and 1 < first_job.end;
        instantiate(forall (j: int32) { first_job.begin <= j and j < first_job.end implies first_job.output[j] == first_job.value }, 1);
        close();
    }
    have output[0] == 11;
    have output[1] == 11 by {
        instantiate(forall (j: int32) { 0 <= j and j < 2 implies output[j] == 11 }, 1);
        close();
    }
    step();
    unfold(filled_range(output, 2, 4, 22));
    have range_filled(&second_job);
    have forall (k: int32) {
        second_job.begin <= k and k < second_job.end implies second_job.output[k] == second_job.value
    } by { unfold(range_filled(&second_job)); close(); }
    have second_job.output[2] == second_job.value by {
        have second_job.begin <= 2 and 2 < second_job.end;
        instantiate(forall (j: int32) { second_job.begin <= j and j < second_job.end implies second_job.output[j] == second_job.value }, 2);
        close();
    }
    have second_job.output[3] == second_job.value by {
        have second_job.begin <= 3 and 3 < second_job.end;
        instantiate(forall (j: int32) { second_job.begin <= j and j < second_job.end implies second_job.output[j] == second_job.value }, 3);
        close();
    }
    have output[2] == 22;
    have output[3] == 22;
    step_until(function.exit);
    close();
}
