verifying "sum.rs";
function prefix(bytes: const uint8*, end: int32) -> Integer {
    (0..end).fold(0, |acc, k| {
        acc + to_integer((int32)bytes[k])
    })
}
fn sum(bytes: &[u8]) -> i32 {
    requires bytes_len <= 1000u64;
    views bytes[0..(int32)(uint32)bytes_len];
    ensures to_integer(result) == old(prefix(bytes, (int32)(uint32)bytes_len));
} by {
    execute_until(loop(0));
    have 0 <= (int32)(uint32)bytes_len by { simp(); }
    have viewable(bytes[0..(int32)(uint32)bytes_len]) by {
        transport(at(function.entry, viewable(bytes[0..(int32)(uint32)bytes_len])), viewable(bytes[0..(int32)(uint32)bytes_len])) using {
            at(function.entry, viewable(bytes[0..(int32)(uint32)bytes_len]));
            0 <= (int32)(uint32)bytes_len;
        }
    }
    have prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining)) == 0 by {
        peel(prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining))) using {
            0 >= ((int32)(uint32)bytes_len - iter_remaining);
        } simp();
    }
    have to_integer(total) == 0 by {
        simp();
    }
    have to_integer(total) == prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining)) by {
        arithmetic() using {
            to_integer(total) == 0;
            prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining)) == 0;
        }
    }
    # This sidecar chooses an input-prefix invariant; the iterator supplies
    # its remaining slice and cursor, without a processed-count variable.
    loop {
        decreases iter_remaining;
        views bytes[0..(int32)(uint32)bytes_len];
        invariant viewable(bytes[0..(int32)(uint32)bytes_len]);
        invariant bytes_len <= 1000u64;
        invariant 0 <= iter_remaining and iter_remaining <= (int32)(uint32)bytes_len;
        invariant 0 <= (int32)(uint32)bytes_len and 1000 >= (int32)(uint32)bytes_len;
        invariant iter_cursor == bytes + ((int32)(uint32)bytes_len - iter_remaining);
        invariant 0 <= ((int32)(uint32)bytes_len - iter_remaining) and 1000 >= ((int32)(uint32)bytes_len - iter_remaining);
        invariant 0 <= to_integer(total) and to_integer(total) <= 255 * to_integer(((int32)(uint32)bytes_len - iter_remaining));
        invariant to_integer(total) == prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining));
        preserve by {
            mark iteration;
            have 0 < iter_remaining by { simp(); }
            have 0 <= iter_remaining - 1 by { arithmetic() using { 0 < iter_remaining; } }
            have 0 <= to_integer(((int32)(uint32)bytes_len - iter_remaining)) by {
                apply(int32_less_equal_to_integer(0, ((int32)(uint32)bytes_len - iter_remaining))) using {
                    0 <= ((int32)(uint32)bytes_len - iter_remaining);
                }
            }
            have to_integer(((int32)(uint32)bytes_len - iter_remaining)) <= 1000 by {
                apply(int32_less_equal_to_integer(((int32)(uint32)bytes_len - iter_remaining), 1000)) using {
                    1000 >= ((int32)(uint32)bytes_len - iter_remaining);
                }
            }
            have to_integer(total) <= 255000 by {
                arithmetic() using {
                    to_integer(total) <= 255 * to_integer(((int32)(uint32)bytes_len - iter_remaining));
                    to_integer(((int32)(uint32)bytes_len - iter_remaining)) <= 1000;
                }
            }
            have iter_remaining - 1 <= (int32)(uint32)bytes_len by {
                apply(int32_nonnegative_predecessor_upper_bound(iter_remaining, (int32)(uint32)bytes_len)) using {
                    0 <= iter_remaining;
                    iter_remaining <= (int32)(uint32)bytes_len;
                }
            }
            execute_until(read(0));
            have 0 <= iter_remaining by { simp(); }
            have iter_remaining <= (int32)(uint32)bytes_len by { simp(); }
            have ((int32)(uint32)bytes_len - iter_remaining - 1) < (int32)(uint32)bytes_len by { arithmetic() using {
                at(iteration, 0 < iter_remaining);
                at(iteration, iter_remaining <= (int32)(uint32)bytes_len);
                0 <= (int32)(uint32)bytes_len; 1000 >= (int32)(uint32)bytes_len;
            } }
            have 0 <= ((int32)(uint32)bytes_len - iter_remaining - 1) by {
                arithmetic() using {
                    at(iteration, 0 < iter_remaining);
                    at(iteration, iter_remaining <= (int32)(uint32)bytes_len);
                    0 <= (int32)(uint32)bytes_len; 1000 >= (int32)(uint32)bytes_len;
                }
            }
            have 0 <= (int32)(uint32)bytes_len by { simp(); }
            have ((int32)(uint32)bytes_len - iter_remaining - 1) == at(iteration, (int32)(uint32)bytes_len - iter_remaining) by {
                arithmetic() using {
                    at(iteration, 0 < iter_remaining);
                    at(iteration, iter_remaining <= (int32)(uint32)bytes_len);
                    0 <= (int32)(uint32)bytes_len; 1000 >= (int32)(uint32)bytes_len;
                }
            }
            have at(iteration, iter_cursor) == bytes + at(iteration, (int32)(uint32)bytes_len - iter_remaining) by { simp(); }
            have at(iteration, iter_cursor) == bytes + ((int32)(uint32)bytes_len - iter_remaining - 1) by {
                rewrite(((int32)(uint32)bytes_len - iter_remaining - 1) == at(iteration, (int32)(uint32)bytes_len - iter_remaining));
                simp();
            }
            step();
            mark loaded;
            have bytes + ((int32)(uint32)bytes_len - iter_remaining - 1) == at(iteration, iter_cursor) by { simp(); }
            have defined((int32)(uint32)bytes_len - iter_remaining) by {
                apply(int32_nonnegative_subtract_within_value_is_defined((int32)(uint32)bytes_len, iter_remaining)) using {
                    0 <= iter_remaining;
                    iter_remaining <= (int32)(uint32)bytes_len;
                } simp();
            }
            have 1 <= (int32)(uint32)bytes_len - iter_remaining by {
                arithmetic() using {
                    at(iteration, 0 < iter_remaining);
                    at(iteration, iter_remaining <= (int32)(uint32)bytes_len);
                    0 <= (int32)(uint32)bytes_len; 1000 >= (int32)(uint32)bytes_len;
                }
            }
            have defined((int32)(uint32)bytes_len - iter_remaining - 1) by {
                apply(int32_nonnegative_subtract_within_value_is_defined((int32)(uint32)bytes_len - iter_remaining, 1)) using {
                    0 <= 1;
                    1 <= (int32)(uint32)bytes_len - iter_remaining;
                } simp();
            }
            have viewable(bytes[0..(int32)(uint32)bytes_len]) by {
                transport(at(iteration, viewable(bytes[0..(int32)(uint32)bytes_len])), viewable(bytes[0..(int32)(uint32)bytes_len])) using {
                    at(iteration, viewable(bytes[0..(int32)(uint32)bytes_len]));
                    0 <= (int32)(uint32)bytes_len;
                }
            }
            have defined(bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) by {
                transport(viewable(bytes[0..(int32)(uint32)bytes_len]), defined(bytes[((int32)(uint32)bytes_len - iter_remaining - 1)])) using {
                    viewable(bytes[0..(int32)(uint32)bytes_len]);
                    defined((int32)(uint32)bytes_len - iter_remaining - 1);
                    0 <= (int32)(uint32)bytes_len;
                    0 <= ((int32)(uint32)bytes_len - iter_remaining - 1);
                    ((int32)(uint32)bytes_len - iter_remaining - 1) < (int32)(uint32)bytes_len;
                }
            }
            have 0 <= (int32)byte and 255 >= (int32)byte by { simp(); }
            have bytes[((int32)(uint32)bytes_len - iter_remaining - 1)] == byte by { simp(); }
            have 0 <= (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)] and 255 >= (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)] by { rewrite(bytes[((int32)(uint32)bytes_len - iter_remaining - 1)] == byte); simp(); }
            have 0 <= to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) by {
                apply(int32_less_equal_to_integer(0, (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)])) using {
                    0 <= (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)];
                }
            }
            have to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) <= 255 by {
                apply(int32_less_equal_to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)], 255)) using {
                    255 >= (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)];
                }
            }
            have to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) >= -2147483648 by {
                arithmetic() using {
                    0 <= to_integer(total);
                    0 <= to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]);
                }
            }
            have to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) <= 2147483647 by {
                arithmetic() using {
                    to_integer(total) <= 255000;
                    to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) <= 255;
                }
            }
            have defined(total + (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) by {
                apply(int32_add_defined_by_integer_bounds(total, (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)])) using {
                    to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) >= -2147483648;
                    to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) <= 2147483647;
                } simp();
            }
            have to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) == to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) by {
                apply(int32_add_to_integer(total, (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)])) using {
                    defined(total + (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]);
                }
            }
            have 1000 >= ((int32)(uint32)bytes_len - iter_remaining - 1) by {
                arithmetic() using {
                    at(iteration, 0 < iter_remaining);
                    at(iteration, iter_remaining <= (int32)(uint32)bytes_len);
                    0 <= (int32)(uint32)bytes_len; 1000 >= (int32)(uint32)bytes_len;
                }
            }
            have to_integer(total) == prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining - 1)) by {
                rewrite(((int32)(uint32)bytes_len - iter_remaining - 1) == at(iteration, (int32)(uint32)bytes_len - iter_remaining)); simp();
            }
            have to_integer(((int32)(uint32)bytes_len - iter_remaining - 1)) == at(iteration, to_integer((int32)(uint32)bytes_len - iter_remaining)) by {
                rewrite(((int32)(uint32)bytes_len - iter_remaining - 1) == at(iteration, (int32)(uint32)bytes_len - iter_remaining)); simp();
            }
            have to_integer(total) <= 255 * to_integer(((int32)(uint32)bytes_len - iter_remaining - 1)) by {
                arithmetic() using {
                    at(iteration, to_integer(total) <= 255 * to_integer((int32)(uint32)bytes_len - iter_remaining));
                    to_integer(((int32)(uint32)bytes_len - iter_remaining - 1)) == at(iteration, to_integer((int32)(uint32)bytes_len - iter_remaining));
                }
            }
            have (((int32)(uint32)bytes_len - iter_remaining - 1)) < 2147483647 by {
                apply(int32_le_lt_transitive(((int32)(uint32)bytes_len - iter_remaining - 1), 1000, 2147483647)) using {
                    1000 >= ((int32)(uint32)bytes_len - iter_remaining - 1);
                    1000 < 2147483647;
                }
            }
            have prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining - 1) + 1) == prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining - 1)) + to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) by {
                peel(prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining - 1) + 1)) using {
                    0 <= ((int32)(uint32)bytes_len - iter_remaining - 1);
                    (((int32)(uint32)bytes_len - iter_remaining - 1)) < 2147483647;
                }
                simp();
            }
            have to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) == prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining - 1) + 1) by {
                arithmetic() using {
                    to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) == to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]);
                    to_integer(total) == prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining - 1));
                    prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining - 1) + 1) == prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining - 1)) + to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]);
                }
            }
            have defined(((int32)(uint32)bytes_len - iter_remaining - 1) + 1) by {
                apply(int32_increment_below_max_is_defined(((int32)(uint32)bytes_len - iter_remaining - 1))) using {
                    (((int32)(uint32)bytes_len - iter_remaining - 1)) < 2147483647;
                } simp();
            }
            have to_integer(((int32)(uint32)bytes_len - iter_remaining - 1) + 1) == to_integer(((int32)(uint32)bytes_len - iter_remaining - 1)) + 1 by {
                apply(int32_add_to_integer(((int32)(uint32)bytes_len - iter_remaining - 1), 1)) using {
                    defined(((int32)(uint32)bytes_len - iter_remaining - 1) + 1);
                }
            }
            have 0 <= to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) by {
                arithmetic() using {
                    0 <= to_integer(total);
                    0 <= to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]);
                }
            }
            have 0 <= to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) by {
                arithmetic() using {
                    0 <= to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]);
                    to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) == to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]);
                }
            }
            have to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) <= 255 * (to_integer(((int32)(uint32)bytes_len - iter_remaining - 1)) + 1) by {
                arithmetic() using {
                    to_integer(total) <= 255 * to_integer(((int32)(uint32)bytes_len - iter_remaining - 1));
                    to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) <= 255;
                }
            }
            have to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) <= 255 * to_integer(((int32)(uint32)bytes_len - iter_remaining - 1) + 1) by {
                arithmetic() using {
                    to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) <= 255 * (to_integer(((int32)(uint32)bytes_len - iter_remaining - 1)) + 1);
                    to_integer(((int32)(uint32)bytes_len - iter_remaining - 1) + 1) == to_integer(((int32)(uint32)bytes_len - iter_remaining - 1)) + 1;
                }
            }
            have to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) <= 255 * to_integer(((int32)(uint32)bytes_len - iter_remaining - 1) + 1) by {
                arithmetic() using {
                    to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) <= 255 * to_integer(((int32)(uint32)bytes_len - iter_remaining - 1) + 1);
                    to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) == to_integer(total) + to_integer((int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]);
                }
            }
            have ((int32)(uint32)bytes_len - iter_remaining) == ((int32)(uint32)bytes_len - iter_remaining - 1) + 1 by {
                arithmetic() using {
                    at(iteration, 0 < iter_remaining);
                    at(iteration, iter_remaining <= (int32)(uint32)bytes_len);
                    0 <= (int32)(uint32)bytes_len; 1000 >= (int32)(uint32)bytes_len;
                }
            }
            have at(iteration, (int32)(uint32)bytes_len - iter_remaining) < 2147483647 by {
                apply(int32_le_lt_transitive(at(iteration, (int32)(uint32)bytes_len - iter_remaining), 1000, 2147483647)) using {
                    at(iteration, 1000 >= ((int32)(uint32)bytes_len - iter_remaining));
                    1000 < 2147483647;
                }
            }
            have at(iteration, iter_cursor) + 1 == bytes + (at(iteration, (int32)(uint32)bytes_len - iter_remaining) + 1) by {
                arithmetic() using {
                    at(iteration, iter_cursor) == bytes + at(iteration, (int32)(uint32)bytes_len - iter_remaining);
                    at(iteration, (int32)(uint32)bytes_len - iter_remaining) < 2147483647;
                }
            }
            have ((int32)(uint32)bytes_len - iter_remaining) == at(iteration, (int32)(uint32)bytes_len - iter_remaining) + 1 by {
                arithmetic() using {
                    at(iteration, 0 < iter_remaining);
                    at(iteration, iter_remaining <= (int32)(uint32)bytes_len);
                    0 <= (int32)(uint32)bytes_len; 1000 >= (int32)(uint32)bytes_len;
                }
            }
            have iter_cursor == bytes + ((int32)(uint32)bytes_len - iter_remaining) by {
                rewrite(((int32)(uint32)bytes_len - iter_remaining) == at(iteration, (int32)(uint32)bytes_len - iter_remaining) + 1);
                simp();
            }
            have to_integer((int32)(uint32)bytes_len - iter_remaining) == to_integer(((int32)(uint32)bytes_len - iter_remaining - 1) + 1) by {
                rewrite(((int32)(uint32)bytes_len - iter_remaining) == ((int32)(uint32)bytes_len - iter_remaining - 1) + 1); simp();
            }
            have to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) <= 255 * to_integer((int32)(uint32)bytes_len - iter_remaining) by {
                arithmetic() using {
                    to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) <= 255 * to_integer(((int32)(uint32)bytes_len - iter_remaining - 1) + 1);
                    to_integer((int32)(uint32)bytes_len - iter_remaining) == to_integer(((int32)(uint32)bytes_len - iter_remaining - 1) + 1);
                }
            }
            have prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining - 1) + 1) == prefix(bytes, (int32)(uint32)bytes_len - iter_remaining) by {
                rewrite(((int32)(uint32)bytes_len - iter_remaining) == ((int32)(uint32)bytes_len - iter_remaining - 1) + 1); simp();
            }
            have defined(total + (int32)byte) by { simp(); }
            have to_integer(total + (int32)byte) == to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) by { rewrite(bytes[((int32)(uint32)bytes_len - iter_remaining - 1)] == byte); simp(); }
            have 0 <= to_integer(total + (int32)byte) by {
                arithmetic() using {
                    to_integer(total + (int32)byte) == to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]);
                    0 <= to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]);
                }
            }
            have to_integer(total + (int32)byte) <= 255 * to_integer(((int32)(uint32)bytes_len - iter_remaining)) by {
                arithmetic() using {
                    to_integer(total + (int32)byte) == to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]);
                    to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) <= 255 * to_integer(((int32)(uint32)bytes_len - iter_remaining));
                }
            }
            have to_integer(total + (int32)byte) == prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining)) by {
                arithmetic() using {
                    to_integer(total + (int32)byte) == to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]);
                    to_integer(total + (int32)bytes[((int32)(uint32)bytes_len - iter_remaining - 1)]) == prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining - 1) + 1);
                    prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining - 1) + 1) == prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining));
                }
            }
            mark addition;
            execute_until(assignment(total, 1)); step();
            have to_integer(total) == at(addition, to_integer(total + (int32)byte)) by { simp(); }
            execute_until(back_edge());
            have viewable(bytes[0..(int32)(uint32)bytes_len]) by {
                transport(at(loaded, viewable(bytes[0..(int32)(uint32)bytes_len])), viewable(bytes[0..(int32)(uint32)bytes_len])) using {
                    at(loaded, viewable(bytes[0..(int32)(uint32)bytes_len]));
                    0 <= (int32)(uint32)bytes_len;
                }
            }
            have 0 <= to_integer(total) by { arithmetic() using { to_integer(total) == at(addition, to_integer(total + (int32)byte)); at(addition, 0 <= to_integer(total + (int32)byte)); } }
            have to_integer(((int32)(uint32)bytes_len - iter_remaining)) == at(addition, to_integer(((int32)(uint32)bytes_len - iter_remaining))) by { simp(); }
            have to_integer(total) <= 255 * to_integer(((int32)(uint32)bytes_len - iter_remaining)) by {
                arithmetic() using {
                    to_integer(total) == at(addition, to_integer(total + (int32)byte));
                    at(addition, to_integer(total + (int32)byte) <= 255 * to_integer(((int32)(uint32)bytes_len - iter_remaining)));
                    to_integer(((int32)(uint32)bytes_len - iter_remaining)) == at(addition, to_integer(((int32)(uint32)bytes_len - iter_remaining)));
                }
            }
            have prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining)) == at(addition, prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining))) by { simp(); }
            have to_integer(total) == prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining)) by {
                arithmetic() using {
                    to_integer(total) == at(addition, to_integer(total + (int32)byte));
                    at(addition, to_integer(total + (int32)byte) == prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining)));
                    prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining)) == at(addition, prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining)));
                }
            }
            close_invariants();
        }
    }
    have iter_remaining == 0 by { simp(); }
    have ((int32)(uint32)bytes_len - iter_remaining) == (int32)(uint32)bytes_len by { simp(); }
    have prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining)) == prefix(bytes, (int32)(uint32)bytes_len) by {
        rewrite(((int32)(uint32)bytes_len - iter_remaining) == (int32)(uint32)bytes_len); simp();
    }
    have to_integer(total) == prefix(bytes, (int32)(uint32)bytes_len) by {
        arithmetic() using {
            to_integer(total) == prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining));
            prefix(bytes, ((int32)(uint32)bytes_len - iter_remaining)) == prefix(bytes, (int32)(uint32)bytes_len);
        }
    }
    execute();
    simp();
}
