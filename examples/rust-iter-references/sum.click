verifying "sum.rs";
function prefix(bytes: const uint8*, end: int32) -> Integer {
    (0..end).fold(0, |acc, k| {
        acc + to_integer((int32)bytes[k])
    })
}
int32 sum(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len <= 1000u64;
    views bytes[0..(int32)(uint32)bytes_len];
    ensures to_integer(result) == old(prefix(bytes, (int32)(uint32)bytes_len));
} by {
    execute_until(statement(7));
    have prefix(bytes, (int32)(uint32)__rust_iter_index_3_5) == 0 by {
        unfold(prefix(bytes, (int32)(uint32)__rust_iter_index_3_5)) using {
            0 >= (int32)(uint32)__rust_iter_index_3_5;
        } simp();
    }
    have to_integer(total) == 0 by {
        simp();
    }
    have to_integer(total) == prefix(bytes, (int32)(uint32)__rust_iter_index_3_5) by {
        arithmetic() using {
            to_integer(total) == 0;
            prefix(bytes, (int32)(uint32)__rust_iter_index_3_5) == 0;
        }
    }
    loop {
        decreases bytes_len - __rust_iter_index_3_5;
        views bytes[0..(int32)(uint32)bytes_len];
        invariant __rust_iter_index_3_5 <= bytes_len;
        invariant bytes_len <= 1000u64;
        invariant 0 <= (int32)(uint32)__rust_iter_index_3_5 and 1000 >= (int32)(uint32)__rust_iter_index_3_5;
        invariant 0 <= to_integer(total) and to_integer(total) <= 255 * to_integer((int32)(uint32)__rust_iter_index_3_5);
        invariant to_integer(total) == prefix(bytes, (int32)(uint32)__rust_iter_index_3_5);
        preserve by {
            have bytes_len <= 2147483647u64 by {
                normalize() using {
                    bytes_len <= 1000u64;
                }
            }
            have 0 <= to_integer((int32)(uint32)__rust_iter_index_3_5) by {
                apply(int32_less_equal_to_integer(0, (int32)(uint32)__rust_iter_index_3_5)) using {
                    0 <= (int32)(uint32)__rust_iter_index_3_5;
                }
            }
            have to_integer((int32)(uint32)__rust_iter_index_3_5) <= 1000 by {
                apply(int32_less_equal_to_integer((int32)(uint32)__rust_iter_index_3_5, 1000)) using {
                    1000 >= (int32)(uint32)__rust_iter_index_3_5;
                }
            }
            have to_integer(total) <= 255000 by {
                arithmetic() using {
                    to_integer(total) <= 255 * to_integer((int32)(uint32)__rust_iter_index_3_5);
                    to_integer((int32)(uint32)__rust_iter_index_3_5) <= 1000;
                }
            }
            execute_until(statement(21));
            have ((int32)(uint32)__rust_iter_index_3_5) < (int32)(uint32)bytes_len by {
                simp() using {
                    __rust_iter_index_3_5 < bytes_len;
                    bytes_len <= 2147483647u64;
                }
            }
            have 0 <= (int32)(uint32)__rust_iter_index_3_5 by {
                simp();
            }
            have 0 <= (int32)(uint32)bytes_len by {
                simp();
            }
            have 0 <= (int32)bytes[(int32)(uint32)__rust_iter_index_3_5] and 255 >= (int32)bytes[(int32)(uint32)__rust_iter_index_3_5] by {
                simp();
            }
            have defined(bytes[(int32)(uint32)__rust_iter_index_3_5]) by {
                transport(at(function.entry, viewable(bytes[0..(int32)(uint32)bytes_len])), defined(bytes[(int32)(uint32)__rust_iter_index_3_5])) using {
                    at(function.entry, viewable(bytes[0..(int32)(uint32)bytes_len]));
                    0 <= (int32)(uint32)bytes_len;
                    0 <= (int32)(uint32)__rust_iter_index_3_5;
                    ((int32)(uint32)__rust_iter_index_3_5) < (int32)(uint32)bytes_len;
                }
            }
            have 0 <= to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) by {
                apply(int32_less_equal_to_integer(0, (int32)bytes[(int32)(uint32)__rust_iter_index_3_5])) using {
                    0 <= (int32)bytes[(int32)(uint32)__rust_iter_index_3_5];
                }
            }
            have to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) <= 255 by {
                apply(int32_less_equal_to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5], 255)) using {
                    255 >= (int32)bytes[(int32)(uint32)__rust_iter_index_3_5];
                }
            }
            have to_integer(total) + to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) >= -2147483648 by {
                arithmetic() using {
                    0 <= to_integer(total);
                    0 <= to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]);
                }
            }
            have to_integer(total) + to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) <= 2147483647 by {
                arithmetic() using {
                    to_integer(total) <= 255000;
                    to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) <= 255;
                }
            }
            have defined(total + (int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) by {
                apply(int32_add_defined_by_integer_bounds(total, (int32)bytes[(int32)(uint32)__rust_iter_index_3_5])) using {
                    to_integer(total) + to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) >= -2147483648;
                    to_integer(total) + to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) <= 2147483647;
                } simp();
            }
            have to_integer(total + (int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) == to_integer(total) + to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) by {
                apply(int32_add_to_integer(total, (int32)bytes[(int32)(uint32)__rust_iter_index_3_5])) using {
                    defined(total + (int32)bytes[(int32)(uint32)__rust_iter_index_3_5]);
                }
            }
            have ((int32)(uint32)__rust_iter_index_3_5) < 2147483647 by {
                apply(int32_le_lt_transitive((int32)(uint32)__rust_iter_index_3_5, 1000, 2147483647)) using {
                    1000 >= (int32)(uint32)__rust_iter_index_3_5;
                    1000 < 2147483647;
                }
            }
            have prefix(bytes, (int32)(uint32)__rust_iter_index_3_5 + 1) == prefix(bytes, (int32)(uint32)__rust_iter_index_3_5) + to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) by {
                unfold(prefix(bytes, (int32)(uint32)__rust_iter_index_3_5 + 1)) using {
                    0 <= (int32)(uint32)__rust_iter_index_3_5;
                    ((int32)(uint32)__rust_iter_index_3_5) < 2147483647;
                }
                simp();
            }
            have to_integer(total + (int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) == prefix(bytes, (int32)(uint32)__rust_iter_index_3_5 + 1) by {
                arithmetic() using {
                    to_integer(total + (int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) == to_integer(total) + to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]);
                    to_integer(total) == prefix(bytes, (int32)(uint32)__rust_iter_index_3_5);
                    prefix(bytes, (int32)(uint32)__rust_iter_index_3_5 + 1) == prefix(bytes, (int32)(uint32)__rust_iter_index_3_5) + to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]);
                }
            }
            have defined((int32)(uint32)__rust_iter_index_3_5 + 1) by {
                apply(int32_increment_below_max_is_defined((int32)(uint32)__rust_iter_index_3_5)) using {
                    ((int32)(uint32)__rust_iter_index_3_5) < 2147483647;
                }
            }
            have to_integer((int32)(uint32)__rust_iter_index_3_5 + 1) == to_integer((int32)(uint32)__rust_iter_index_3_5) + 1 by {
                apply(int32_add_to_integer((int32)(uint32)__rust_iter_index_3_5, 1)) using {
                    defined((int32)(uint32)__rust_iter_index_3_5 + 1);
                }
            }
            have 0 <= to_integer(total) + to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) by {
                arithmetic() using {
                    0 <= to_integer(total);
                    0 <= to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]);
                }
            }
            have 0 <= to_integer(total + (int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) by {
                arithmetic() using {
                    0 <= to_integer(total) + to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]);
                    to_integer(total + (int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) == to_integer(total) + to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]);
                }
            }
            have to_integer(total) + to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) <= 255 * (to_integer((int32)(uint32)__rust_iter_index_3_5) + 1) by {
                arithmetic() using {
                    to_integer(total) <= 255 * to_integer((int32)(uint32)__rust_iter_index_3_5);
                    to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) <= 255;
                }
            }
            have to_integer(total) + to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) <= 255 * to_integer((int32)(uint32)__rust_iter_index_3_5 + 1) by {
                arithmetic() using {
                    to_integer(total) + to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) <= 255 * (to_integer((int32)(uint32)__rust_iter_index_3_5) + 1);
                    to_integer((int32)(uint32)__rust_iter_index_3_5 + 1) == to_integer((int32)(uint32)__rust_iter_index_3_5) + 1;
                }
            }
            have to_integer(total + (int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) <= 255 * to_integer((int32)(uint32)__rust_iter_index_3_5 + 1) by {
                arithmetic() using {
                    to_integer(total) + to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) <= 255 * to_integer((int32)(uint32)__rust_iter_index_3_5 + 1);
                    to_integer(total + (int32)bytes[(int32)(uint32)__rust_iter_index_3_5]) == to_integer(total) + to_integer((int32)bytes[(int32)(uint32)__rust_iter_index_3_5]);
                }
            }
            execute_until(statement(29));
            step();
            have __rust_iter_index_3_5 <= bytes_len by {
                simp();
            }
            have __rust_iter_index_3_5 <= 1000u64 by {
                normalize() using {
                    __rust_iter_index_3_5 <= bytes_len;
                    bytes_len <= 1000u64;
                }
            }
            have __rust_iter_index_3_5 <= 2147483647u64 by {
                normalize() using {
                    __rust_iter_index_3_5 <= 1000u64;
                }
            }
            have 0 <= (int32)(uint32)__rust_iter_index_3_5 by {
                normalize() using {
                    __rust_iter_index_3_5 <= 2147483647u64;
                }
            }
            have 1000 >= (int32)(uint32)__rust_iter_index_3_5 by {
                normalize() using {
                    __rust_iter_index_3_5 <= 1000u64;
                }
            }
            close_invariants();
        }
    }
    have __rust_iter_index_3_5 == bytes_len by {
        simp() using {
            __rust_iter_index_3_5 <= bytes_len;
            not __rust_iter_index_3_5 < bytes_len;
        }
    }
    have ((int32)(uint32)__rust_iter_index_3_5) == (int32)(uint32)bytes_len by {
        normalize() using {
            __rust_iter_index_3_5 == bytes_len;
        }
    }
    have prefix(bytes, (int32)(uint32)__rust_iter_index_3_5) == prefix(bytes, (int32)(uint32)bytes_len) by {
        rewrite(((int32)(uint32)__rust_iter_index_3_5) == (int32)(uint32)bytes_len);
        simp();
    }
    have to_integer(total) == prefix(bytes, (int32)(uint32)bytes_len) by {
        arithmetic() using {
            to_integer(total) == prefix(bytes, (int32)(uint32)__rust_iter_index_3_5);
            prefix(bytes, (int32)(uint32)__rust_iter_index_3_5) == prefix(bytes, (int32)(uint32)bytes_len);
        }
    }
    execute();
    simp();
}
