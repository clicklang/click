// Foundational Integer order laws, available through ordinary explicit application.
axiom add_le(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a <= b;
    requires c <= d;
    ensures a + c <= b + d;
}

axiom le_antisymmetric(a: Integer, b: Integer) {
    requires a <= b;
    requires b <= a;
    ensures a == b;
}

// Discreteness of exact Integer order, already used by strict arithmetic
// certificate premises. The reverse implication is proved below.
axiom lt_step_le(a: Integer, b: Integer) {
    requires a < b;
    ensures a + 1 <= b;
}

theorem step_le_lt(a: Integer, b: Integer) {
    requires a + 1 <= b;
    ensures a < b by {
        if a < b {
            known();
        } else {
            have b <= a by { normalize() using { not (a < b); }; }
            have a + 1 + b <= b + a by {
                apply(integer::add_le(a + 1, b, b, a)) using { a + 1 <= b; b <= a; };
            }
            contradiction(a + 1 + b <= b + a);
        }
    }
}

theorem le_ne_lt(a: Integer, b: Integer) {
    requires a <= b;
    requires a != b;
    ensures a < b by {
        if a < b {
            known();
        } else {
            have b <= a by { normalize() using { not (a < b); }; }
            have a == b by {
                apply(integer::le_antisymmetric(a, b)) using { a <= b; b <= a; };
            }
            contradiction(a == b);
        }
    }
}

// Congruence helpers are ordinary proved theorems. Applying a generic
// substitution theorem also works when a concrete equality evaluates to true.
theorem le_substitute(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a <= b;
    requires c == a;
    requires d == b;
    ensures c <= d by { normalize() using { a <= b; c == a; d == b; }; }
}

theorem equal_substitute(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a == b;
    requires c == a;
    requires d == b;
    ensures c == d by { normalize() using { a == b; c == a; d == b; }; }
}

theorem le_difference(a:Integer,b:Integer,value:Integer) {
 requires a<=b;
 requires value==a-b;
 ensures value<=0 by {
  have a + -b <= b + -b by {
   apply(click::integer::add_le(a,b,-b,-b)) using {a<=b;-b<=-b;};
  }
  have value == a + -b by { rewrite(value,a-b); normalize(); }
  have 0 == b + -b by normalize();
  apply(click::integer::le_substitute(a + -b,b + -b,value,0)) using {a + -b <= b + -b; value==a + -b;0==b + -b;};
 }
}
theorem difference_le(a:Integer,b:Integer,value:Integer) {
 requires value<=0;
 requires value==a-b;
 ensures a<=b by {
  have value + b <= 0 + b by {
   apply(click::integer::add_le(value,0,b,b)) using {value<=0;b<=b;};
  }
  have a == value + b by { rewrite(value,a-b); normalize(); }
  have b == 0 + b by normalize();
  apply(click::integer::le_substitute(value+b,0+b,a,b)) using {value+b<=0+b;a==value+b;b==0+b;};
 }
}

theorem equal_difference(a: Integer, b: Integer) {
    requires a == b;
    ensures a - b == 0 by { rewrite(a, b); normalize(); }
}

theorem equal_add(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a == b;
    requires c == d;
    ensures a + c == b + d by { normalize() using { a == b; c == d; }; }
}

theorem equal_multiply(a: Integer, b: Integer, factor: Integer) {
    requires a == b;
    ensures a * factor == b * factor by { normalize() using { a == b; }; }
}

theorem equal_le(a: Integer, b: Integer) {
    requires a == b;
    ensures a <= b by { rewrite(a, b); normalize(); }
}

// No nonnegativity assumption on the remainder is needed for this upper
// bound. The strict upper bound and positive divisor are both essential.
axiom round_down_le(value: Integer, bound: Integer, divisor: Integer, remainder: Integer) {
    requires 0 < divisor;
    requires remainder < divisor;
    requires value * divisor <= bound * divisor + remainder;
    ensures value <= bound;
}

theorem int32_increment_upper_bound(value: int32, upper: int32) {
    requires value < upper;

    ensures to_integer(value + 1) <= to_integer(upper) by {
        have to_integer((upper as int32)) <= to_integer((2147483647 as int32)) by {
            normalize() using {};
        }
        have (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) < (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))) by {
            have (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) < (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))) by {
                have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1) <= 0 by {
                    have to_integer((((value as int32) as int32) as int32)) < to_integer((((upper as int32) as int32) as int32)) by {
                        normalize() using {
                            ((value as int32) as int32) < ((upper as int32) as int32);
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + 1) <= to_integer((((upper as int32) as int32) as int32)) by {
                        apply(click::integer::lt_step_le(to_integer((((value as int32) as int32) as int32)), to_integer((((upper as int32) as int32) as int32)))) using {
                            to_integer((((value as int32) as int32) as int32)) < to_integer((((upper as
                                int32) as int32) as int32));
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1) == ((to_integer((((value as int32) as int32) as int32)) + 1) - to_integer((((upper as int32) as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer((((value as int32) as int32) as int32)) + 1), to_integer((((upper as int32) as int32) as int32)), (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1))) using {
                        (to_integer((((value as int32) as int32) as int32)) + 1) <= to_integer((((upper
                            as int32) as int32) as int32));
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper
                            as int32) as int32) as int32))) + 1) == ((to_integer((((value as int32) as
                            int32) as int32)) + 1) - to_integer((((upper as int32) as int32) as
                            int32)));
                    };
                }
                have (to_integer((((upper as int32) as int32) as int32)) + -2147483647) <= 0 by {
                    have (to_integer((((upper as int32) as int32) as int32)) + -2147483647) == (to_integer((upper as int32)) - to_integer((2147483647 as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((upper as int32)), to_integer((2147483647 as int32)), (to_integer((((upper as int32) as int32) as int32)) + -2147483647))) using {
                        to_integer((upper as int32)) <= to_integer((2147483647 as int32));
                        (to_integer((((upper as int32) as int32) as int32)) + -2147483647) ==
                            (to_integer((upper as int32)) - to_integer((2147483647 as int32)));
                    };
                }
                have (to_integer((((value as int32) as int32) as int32)) + -2147483646) <= 0 by {
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as int32) as int32)) + -2147483647)) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1), 0, (to_integer((((upper as int32) as int32) as int32)) + -2147483647), 0)) using {
                            (to_integer((((value as int32) as int32) as int32)) + (-1 *
                                to_integer((((upper as int32) as int32) as int32))) + 1) <= 0;
                            (to_integer((((upper as int32) as int32) as int32)) + -2147483647) <= 0;
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + -2147483646) == (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as int32) as int32)) + -2147483647)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as int32) as int32)) + -2147483647)), (0 + 0), (to_integer((((value as int32) as int32) as int32)) + -2147483646), 0)) using {
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper
                            as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as
                            int32) as int32)) + -2147483647)) <= (0 + 0);
                        (to_integer((((value as int32) as int32) as int32)) + -2147483646) ==
                            (to_integer((((value as int32) as int32) as int32)) + (-1 *
                            to_integer((((upper as int32) as int32) as int32))) + 1 +
                            (to_integer((((upper as int32) as int32) as int32)) + -2147483647));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer((((value as int32) as int32) as int32)) + -2147483646) == ((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) - (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))), (to_integer((((value as int32) as int32) as int32)) + -2147483646))) using {
                    (to_integer((((value as int32) as int32) as int32)) + -2147483646) <= 0;
                    (to_integer((((value as int32) as int32) as int32)) + -2147483646) ==
                        ((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) -
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))));
                };
                apply(click::integer::step_le_lt((to_integer(((value as int32) as int32)) + to_integer((upper as int32))), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))))) using {
                    (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) <=
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)));
                };
            }
            normalize() using {
                (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) <
                    (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)));
            };
        }
        have -2147483648 <= to_integer((value as int32)) by {
            normalize() using {
                (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) <
                    (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)));
            };
        }
        have to_integer((value as int32)) <= 2147483646 by {
            have to_integer((value as int32)) <= 2147483646 by {
                have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1) <= 0 by {
                    have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) <= (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))) by {
                        apply(click::integer::lt_step_le((to_integer(((value as int32) as int32)) + to_integer((upper as int32))), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))))) using {
                            (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) <
                                (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as
                                int32)));
                        };
                    }
                    have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1) == ((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) - (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))), (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1))) using {
                        (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) <=
                            (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as
                            int32)));
                        (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 *
                            (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as
                            int32)))) + 1) == ((to_integer(((value as int32) as int32)) +
                            to_integer((upper as int32)) + 1) - (to_integer(((upper as int32) as int32))
                            + to_integer((2147483647 as int32))));
                    };
                }
                have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1) == (to_integer((value as int32)) - 2147483646) by {
                    normalize();
                }
                apply(click::integer::difference_le(to_integer((value as int32)), 2147483646, (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1))) using {
                    (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 *
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) +
                        1) <= 0;
                    (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 *
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) +
                        1) == (to_integer((value as int32)) - 2147483646);
                };
            }
            normalize() using {
                to_integer((value as int32)) <= 2147483646;
            };
        }
        have 1 <= to_integer((1 as int32)) by {
            normalize() using {};
        }
        have to_integer((1 as int32)) <= 1 by {
            normalize() using {};
        }
        have -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32))) by {
            have -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32))) by {
                have ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) == (-2147483648 - to_integer((value as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(-2147483648, to_integer((value as int32)), ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)))) using {
                        -2147483648 <= to_integer((value as int32));
                        ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) ==
                            (-2147483648 - to_integer((value as int32)));
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le(((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                        };
                    }
                    have ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute(((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)), 0)) using {
                        ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let
                            integer_constant: Integer = -1; integer_constant)) <= (0 + 0);
                        ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == ((-1 *
                            to_integer((value as int32))) + -to_integer(2147483648u64) + (let
                            integer_constant: Integer = -1; integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == (-2147483648 - (to_integer((value as int32)) + to_integer((1 as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le(-2147483648, (to_integer((value as int32)) + to_integer((1 as int32))), ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)))) using {
                    ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) <= 0;
                    ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == (-2147483648 -
                        (to_integer((value as int32)) + to_integer((1 as int32))));
                };
            }
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32)));
            };
        }
        have (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647 by {
            have (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647 by {
                have (to_integer((value as int32)) + -2147483646) <= 0 by {
                    have (to_integer((value as int32)) + -2147483646) == (to_integer((value as int32)) - 2147483646) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((value as int32)), 2147483646, (to_integer((value as int32)) + -2147483646))) using {
                        to_integer((value as int32)) <= 2147483646;
                        (to_integer((value as int32)) + -2147483646) == (to_integer((value as int32)) -
                            2147483646);
                    };
                }
                have (to_integer((value as int32)) + -2147483646) == ((to_integer((value as int32)) + to_integer((1 as int32))) - 2147483647) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer((value as int32)) + to_integer((1 as int32))), 2147483647, (to_integer((value as int32)) + -2147483646))) using {
                    (to_integer((value as int32)) + -2147483646) <= 0;
                    (to_integer((value as int32)) + -2147483646) == ((to_integer((value as int32)) +
                        to_integer((1 as int32))) - 2147483647);
                };
            }
            normalize() using {
                (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647;
            };
        }
        have defined((value + 1)) by {
            known();
        }
        have to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as int32))) by {
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32)));
                (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647;
            };
        }
        have -2147483647 <= to_integer(((value + 1) as int32)) by {
            normalize() using {
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483646;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        have to_integer(((value + 1) as int32)) <= 2147483647 by {
            normalize() using {
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483646;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        have ((value + 1) as int32) <= (upper as int32) by {
            have defined(((value + 1) as int32)) by {
                known();
            }
            have defined((value + 1)) by {
                known();
            }
            have defined(old(((value + 1) as int32))) by {
                known();
            }
            have defined(old((value + 1))) by {
                known();
            }
            have to_integer((((value + 1) as int32) as int32)) <= to_integer(((upper as int32) as int32)) by {
                have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1) <= 0 by {
                    have to_integer((((value as int32) as int32) as int32)) < to_integer((((upper as int32) as int32) as int32)) by {
                        normalize() using {
                            ((value as int32) as int32) < ((upper as int32) as int32);
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + 1) <= to_integer((((upper as int32) as int32) as int32)) by {
                        apply(click::integer::lt_step_le(to_integer((((value as int32) as int32) as int32)), to_integer((((upper as int32) as int32) as int32)))) using {
                            to_integer((((value as int32) as int32) as int32)) < to_integer((((upper as
                                int32) as int32) as int32));
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1) == ((to_integer((((value as int32) as int32) as int32)) + 1) - to_integer((((upper as int32) as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer((((value as int32) as int32) as int32)) + 1), to_integer((((upper as int32) as int32) as int32)), (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1))) using {
                        (to_integer((((value as int32) as int32) as int32)) + 1) <= to_integer((((upper
                            as int32) as int32) as int32));
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper
                            as int32) as int32) as int32))) + 1) == ((to_integer((((value as int32) as
                            int32) as int32)) + 1) - to_integer((((upper as int32) as int32) as
                            int32)));
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) == 0 by {
                    have (to_integer(((value + 1) as int32)) - (to_integer((value as int32)) + to_integer((1 as int32)))) == 0 by {
                        apply(click::integer::equal_difference(to_integer(((value + 1) as int32)), (to_integer((value as int32)) + to_integer((1 as int32))))) using {
                            to_integer(((value + 1) as int32)) == (to_integer((value as int32)) +
                                to_integer((1 as int32)));
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    have ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) == (to_integer(((value + 1) as int32)) - (to_integer((value as int32)) + to_integer((1 as int32)))) by {
                        normalize();
                    }
                    apply(click::integer::equal_substitute((to_integer(((value + 1) as int32)) - (to_integer((value as int32)) + to_integer((1 as int32)))), 0, ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))), 0)) using {
                        (to_integer(((value + 1) as int32)) - (to_integer((value as int32)) +
                            to_integer((1 as int32)))) == 0;
                        ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) +
                            to_integer(((value + 1) as int32))) == (to_integer(((value + 1) as int32)) -
                            (to_integer((value as int32)) + to_integer((1 as int32))));
                        (let integer_value: Integer = 0; integer_value) == 0;
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) <= 0 by {
                    apply(click::integer::equal_le(((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))), 0)) using {
                        ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) +
                            to_integer(((value + 1) as int32))) == 0;
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have (to_integer((((value as int32) as int32) as int32)) + (-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + (-1 * to_integer((((upper as int32) as int32) as int32))) + to_integer(((value + 1) as int32)) + 1) <= 0 by {
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32)))) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1), 0, ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))), 0)) using {
                            (to_integer((((value as int32) as int32) as int32)) + (-1 *
                                to_integer((((upper as int32) as int32) as int32))) + 1) <= 0;
                            ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) +
                                to_integer(((value + 1) as int32))) <= 0;
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + (-1 * to_integer((((upper as int32) as int32) as int32))) + to_integer(((value + 1) as int32)) + 1) == (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32)))) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32)))), (0 + 0), (to_integer((((value as int32) as int32) as int32)) + (-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + (-1 * to_integer((((upper as int32) as int32) as int32))) + to_integer(((value + 1) as int32)) + 1), 0)) using {
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper
                            as int32) as int32) as int32))) + 1 + ((-1 * (to_integer((value as int32)) +
                            to_integer((1 as int32)))) + to_integer(((value + 1) as int32)))) <= (0 +
                            0);
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * (to_integer((value
                            as int32)) + to_integer((1 as int32)))) + (-1 * to_integer((((upper as
                            int32) as int32) as int32))) + to_integer(((value + 1) as int32)) + 1) ==
                            (to_integer((((value as int32) as int32) as int32)) + (-1 *
                            to_integer((((upper as int32) as int32) as int32))) + 1 + ((-1 *
                            (to_integer((value as int32)) + to_integer((1 as int32)))) +
                            to_integer(((value + 1) as int32))));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have (to_integer((((value as int32) as int32) as int32)) + (-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + (-1 * to_integer((((upper as int32) as int32) as int32))) + to_integer(((value + 1) as int32)) + 1) == (to_integer((((value + 1) as int32) as int32)) - to_integer(((upper as int32) as int32))) by {
                    normalize();
                }
                apply(click::integer::difference_le(to_integer((((value + 1) as int32) as int32)), to_integer(((upper as int32) as int32)), (to_integer((((value as int32) as int32) as int32)) + (-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + (-1 * to_integer((((upper as int32) as int32) as int32))) + to_integer(((value + 1) as int32)) + 1))) using {
                    (to_integer((((value as int32) as int32) as int32)) + (-1 * (to_integer((value as
                        int32)) + to_integer((1 as int32)))) + (-1 * to_integer((((upper as int32) as
                        int32) as int32))) + to_integer(((value + 1) as int32)) + 1) <= 0;
                    (to_integer((((value as int32) as int32) as int32)) + (-1 * (to_integer((value as
                        int32)) + to_integer((1 as int32)))) + (-1 * to_integer((((upper as int32) as
                        int32) as int32))) + to_integer(((value + 1) as int32)) + 1) ==
                        (to_integer((((value + 1) as int32) as int32)) - to_integer(((upper as int32) as
                        int32)));
                    defined(((value + 1) as int32));
                    defined((value + 1));
                    defined(old(((value + 1) as int32)));
                    defined(old((value + 1)));
                };
            }
            normalize() using {
                to_integer((((value + 1) as int32) as int32)) <= to_integer(((upper as int32) as
                    int32));
            };
        }
        have to_integer((value + 1)) <= to_integer(upper) by {
            normalize() using {
                ((value + 1) as int32) <= (upper as int32);
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        known();
    }
}

theorem int32_increment_strictly_increases(value: int32, upper: int32) {
    requires value < upper;

    ensures to_integer(value) < to_integer(value + 1) by {
        have to_integer((upper as int32)) <= to_integer((2147483647 as int32)) by {
            normalize() using {};
        }
        have (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) < (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))) by {
            have (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) < (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))) by {
                have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1) <= 0 by {
                    have to_integer((((value as int32) as int32) as int32)) < to_integer((((upper as int32) as int32) as int32)) by {
                        normalize() using {
                            ((value as int32) as int32) < ((upper as int32) as int32);
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + 1) <= to_integer((((upper as int32) as int32) as int32)) by {
                        apply(click::integer::lt_step_le(to_integer((((value as int32) as int32) as int32)), to_integer((((upper as int32) as int32) as int32)))) using {
                            to_integer((((value as int32) as int32) as int32)) < to_integer((((upper as
                                int32) as int32) as int32));
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1) == ((to_integer((((value as int32) as int32) as int32)) + 1) - to_integer((((upper as int32) as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer((((value as int32) as int32) as int32)) + 1), to_integer((((upper as int32) as int32) as int32)), (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1))) using {
                        (to_integer((((value as int32) as int32) as int32)) + 1) <= to_integer((((upper
                            as int32) as int32) as int32));
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper
                            as int32) as int32) as int32))) + 1) == ((to_integer((((value as int32) as
                            int32) as int32)) + 1) - to_integer((((upper as int32) as int32) as
                            int32)));
                    };
                }
                have (to_integer((((upper as int32) as int32) as int32)) + -2147483647) <= 0 by {
                    have (to_integer((((upper as int32) as int32) as int32)) + -2147483647) == (to_integer((upper as int32)) - to_integer((2147483647 as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((upper as int32)), to_integer((2147483647 as int32)), (to_integer((((upper as int32) as int32) as int32)) + -2147483647))) using {
                        to_integer((upper as int32)) <= to_integer((2147483647 as int32));
                        (to_integer((((upper as int32) as int32) as int32)) + -2147483647) ==
                            (to_integer((upper as int32)) - to_integer((2147483647 as int32)));
                    };
                }
                have (to_integer((((value as int32) as int32) as int32)) + -2147483646) <= 0 by {
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as int32) as int32)) + -2147483647)) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1), 0, (to_integer((((upper as int32) as int32) as int32)) + -2147483647), 0)) using {
                            (to_integer((((value as int32) as int32) as int32)) + (-1 *
                                to_integer((((upper as int32) as int32) as int32))) + 1) <= 0;
                            (to_integer((((upper as int32) as int32) as int32)) + -2147483647) <= 0;
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + -2147483646) == (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as int32) as int32)) + -2147483647)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as int32) as int32)) + -2147483647)), (0 + 0), (to_integer((((value as int32) as int32) as int32)) + -2147483646), 0)) using {
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper
                            as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as
                            int32) as int32)) + -2147483647)) <= (0 + 0);
                        (to_integer((((value as int32) as int32) as int32)) + -2147483646) ==
                            (to_integer((((value as int32) as int32) as int32)) + (-1 *
                            to_integer((((upper as int32) as int32) as int32))) + 1 +
                            (to_integer((((upper as int32) as int32) as int32)) + -2147483647));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer((((value as int32) as int32) as int32)) + -2147483646) == ((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) - (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))), (to_integer((((value as int32) as int32) as int32)) + -2147483646))) using {
                    (to_integer((((value as int32) as int32) as int32)) + -2147483646) <= 0;
                    (to_integer((((value as int32) as int32) as int32)) + -2147483646) ==
                        ((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) -
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))));
                };
                apply(click::integer::step_le_lt((to_integer(((value as int32) as int32)) + to_integer((upper as int32))), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))))) using {
                    (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) <=
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)));
                };
            }
            normalize() using {
                (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) <
                    (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)));
            };
        }
        have -2147483648 <= to_integer((value as int32)) by {
            normalize() using {
                (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) <
                    (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)));
            };
        }
        have to_integer((value as int32)) <= 2147483646 by {
            have to_integer((value as int32)) <= 2147483646 by {
                have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1) <= 0 by {
                    have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) <= (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))) by {
                        apply(click::integer::lt_step_le((to_integer(((value as int32) as int32)) + to_integer((upper as int32))), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))))) using {
                            (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) <
                                (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as
                                int32)));
                        };
                    }
                    have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1) == ((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) - (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))), (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1))) using {
                        (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) <=
                            (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as
                            int32)));
                        (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 *
                            (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as
                            int32)))) + 1) == ((to_integer(((value as int32) as int32)) +
                            to_integer((upper as int32)) + 1) - (to_integer(((upper as int32) as int32))
                            + to_integer((2147483647 as int32))));
                    };
                }
                have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1) == (to_integer((value as int32)) - 2147483646) by {
                    normalize();
                }
                apply(click::integer::difference_le(to_integer((value as int32)), 2147483646, (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1))) using {
                    (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 *
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) +
                        1) <= 0;
                    (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 *
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) +
                        1) == (to_integer((value as int32)) - 2147483646);
                };
            }
            normalize() using {
                to_integer((value as int32)) <= 2147483646;
            };
        }
        have 1 <= to_integer((1 as int32)) by {
            normalize() using {};
        }
        have to_integer((1 as int32)) <= 1 by {
            normalize() using {};
        }
        have -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32))) by {
            have -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32))) by {
                have ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) == (-2147483648 - to_integer((value as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(-2147483648, to_integer((value as int32)), ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)))) using {
                        -2147483648 <= to_integer((value as int32));
                        ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) ==
                            (-2147483648 - to_integer((value as int32)));
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le(((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                        };
                    }
                    have ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute(((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)), 0)) using {
                        ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let
                            integer_constant: Integer = -1; integer_constant)) <= (0 + 0);
                        ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == ((-1 *
                            to_integer((value as int32))) + -to_integer(2147483648u64) + (let
                            integer_constant: Integer = -1; integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == (-2147483648 - (to_integer((value as int32)) + to_integer((1 as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le(-2147483648, (to_integer((value as int32)) + to_integer((1 as int32))), ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)))) using {
                    ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) <= 0;
                    ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == (-2147483648 -
                        (to_integer((value as int32)) + to_integer((1 as int32))));
                };
            }
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32)));
            };
        }
        have (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647 by {
            have (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647 by {
                have (to_integer((value as int32)) + -2147483646) <= 0 by {
                    have (to_integer((value as int32)) + -2147483646) == (to_integer((value as int32)) - 2147483646) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((value as int32)), 2147483646, (to_integer((value as int32)) + -2147483646))) using {
                        to_integer((value as int32)) <= 2147483646;
                        (to_integer((value as int32)) + -2147483646) == (to_integer((value as int32)) -
                            2147483646);
                    };
                }
                have (to_integer((value as int32)) + -2147483646) == ((to_integer((value as int32)) + to_integer((1 as int32))) - 2147483647) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer((value as int32)) + to_integer((1 as int32))), 2147483647, (to_integer((value as int32)) + -2147483646))) using {
                    (to_integer((value as int32)) + -2147483646) <= 0;
                    (to_integer((value as int32)) + -2147483646) == ((to_integer((value as int32)) +
                        to_integer((1 as int32))) - 2147483647);
                };
            }
            normalize() using {
                (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647;
            };
        }
        have defined((value + 1)) by {
            known();
        }
        have to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as int32))) by {
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32)));
                (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647;
            };
        }
        have -2147483647 <= to_integer(((value + 1) as int32)) by {
            normalize() using {
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483646;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        have to_integer(((value + 1) as int32)) <= 2147483647 by {
            normalize() using {
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483646;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        have 0 <= 0 by {
            normalize() using {
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        have (value as int32) < ((value + 1) as int32) by {
            have defined(((value + 1) as int32)) by {
                known();
            }
            have defined((value + 1)) by {
                known();
            }
            have defined(old(((value + 1) as int32))) by {
                known();
            }
            have defined(old((value + 1))) by {
                known();
            }
            have to_integer(((value as int32) as int32)) < to_integer((((value + 1) as int32) as int32)) by {
                have ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) == 0 by {
                    have (to_integer(((value + 1) as int32)) - (to_integer((value as int32)) + to_integer((1 as int32)))) == 0 by {
                        apply(click::integer::equal_difference(to_integer(((value + 1) as int32)), (to_integer((value as int32)) + to_integer((1 as int32))))) using {
                            to_integer(((value + 1) as int32)) == (to_integer((value as int32)) +
                                to_integer((1 as int32)));
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    have ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) == (to_integer(((value + 1) as int32)) - (to_integer((value as int32)) + to_integer((1 as int32)))) by {
                        normalize();
                    }
                    apply(click::integer::equal_substitute((to_integer(((value + 1) as int32)) - (to_integer((value as int32)) + to_integer((1 as int32)))), 0, ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))), 0)) using {
                        (to_integer(((value + 1) as int32)) - (to_integer((value as int32)) +
                            to_integer((1 as int32)))) == 0;
                        ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) +
                            to_integer(((value + 1) as int32))) == (to_integer(((value + 1) as int32)) -
                            (to_integer((value as int32)) + to_integer((1 as int32))));
                        (let integer_value: Integer = 0; integer_value) == 0;
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))) <= 0 by {
                    have (((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) * -1) == (0 * -1) by {
                        apply(click::integer::equal_multiply(((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))), 0, -1)) using {
                            ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) +
                                to_integer(((value + 1) as int32))) == 0;
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))) == 0 by {
                        have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))) == (((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) * -1) by {
                            normalize();
                        }
                        have (let integer_value: Integer = 0; integer_value) == (0 * -1) by {
                            normalize();
                        }
                        apply(click::integer::equal_substitute((((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) * -1), (0 * -1), (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))), 0)) using {
                            (((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) +
                                to_integer(((value + 1) as int32))) * -1) == (0 * -1);
                            (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 *
                                to_integer(((value + 1) as int32)))) == (((-1 * (to_integer((value as
                                int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as
                                int32))) * -1);
                            (let integer_value: Integer = 0; integer_value) == (0 * -1);
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    apply(click::integer::equal_le((to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))), 0)) using {
                        (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 *
                            to_integer(((value + 1) as int32)))) == 0;
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))) == ((to_integer(((value as int32) as int32)) + 1) - to_integer((((value + 1) as int32) as int32))) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer(((value as int32) as int32)) + 1), to_integer((((value + 1) as int32) as int32)), (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))))) using {
                    (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value
                        + 1) as int32)))) <= 0;
                    (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value
                        + 1) as int32)))) == ((to_integer(((value as int32) as int32)) + 1) -
                        to_integer((((value + 1) as int32) as int32)));
                    defined(((value + 1) as int32));
                    defined((value + 1));
                    defined(old(((value + 1) as int32)));
                    defined(old((value + 1)));
                };
                apply(click::integer::step_le_lt(to_integer(((value as int32) as int32)), to_integer((((value + 1) as int32) as int32)))) using {
                    (to_integer(((value as int32) as int32)) + 1) <= to_integer((((value + 1) as int32)
                        as int32));
                    defined(((value + 1) as int32));
                    defined((value + 1));
                    defined(old(((value + 1) as int32)));
                    defined(old((value + 1)));
                };
            }
            normalize() using {
                to_integer(((value as int32) as int32)) < to_integer((((value + 1) as int32) as int32));
            };
        }
        have to_integer(value) < to_integer((value + 1)) by {
            normalize() using {
                (value as int32) < ((value + 1) as int32);
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        known();
    }
}

theorem int32_increment_lower_bound(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures to_integer(lower) <= to_integer(value + 1) by {
        have to_integer((-2147483648 as int32)) <= to_integer((lower as int32)) by {
            normalize() using {};
        }
        have (to_integer(((lower as int32) as int32)) + to_integer((-2147483648 as int32))) <= (to_integer(((value as int32) as int32)) + to_integer((lower as int32))) by {
            have (to_integer(((lower as int32) as int32)) + to_integer((-2147483648 as int32))) <= (to_integer(((value as int32) as int32)) + to_integer((lower as int32))) by {
                have ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32))) <= 0 by {
                    have to_integer((((lower as int32) as int32) as int32)) <= to_integer((((value as int32) as int32) as int32)) by {
                        normalize() using {
                            ((lower as int32) as int32) <= ((value as int32) as int32);
                        };
                    }
                    have ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32))) == (to_integer((((lower as int32) as int32) as int32)) - to_integer((((value as int32) as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((((lower as int32) as int32) as int32)), to_integer((((value as int32) as int32) as int32)), ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32))))) using {
                        to_integer((((lower as int32) as int32) as int32)) <= to_integer((((value as
                            int32) as int32) as int32));
                        ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower
                            as int32) as int32) as int32))) == (to_integer((((lower as int32) as int32)
                            as int32)) - to_integer((((value as int32) as int32) as int32)));
                    };
                }
                have ((-1 * to_integer((((lower as int32) as int32) as int32))) + -to_integer(2147483648u64)) <= 0 by {
                    have ((-1 * to_integer((((lower as int32) as int32) as int32))) + -to_integer(2147483648u64)) == (to_integer((-2147483648 as int32)) - to_integer((lower as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((-2147483648 as int32)), to_integer((lower as int32)), ((-1 * to_integer((((lower as int32) as int32) as int32))) + -to_integer(2147483648u64)))) using {
                        to_integer((-2147483648 as int32)) <= to_integer((lower as int32));
                        ((-1 * to_integer((((lower as int32) as int32) as int32))) +
                            -to_integer(2147483648u64)) == (to_integer((-2147483648 as int32)) -
                            to_integer((lower as int32)));
                    };
                }
                have ((-1 * to_integer((((value as int32) as int32) as int32))) + -to_integer(2147483648u64)) <= 0 by {
                    have ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + ((-1 * to_integer((((lower as int32) as int32) as int32))) + -to_integer(2147483648u64))) <= (0 + 0) by {
                        apply(click::integer::add_le(((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32))), 0, ((-1 * to_integer((((lower as int32) as int32) as int32))) + -to_integer(2147483648u64)), 0)) using {
                            ((-1 * to_integer((((value as int32) as int32) as int32))) +
                                to_integer((((lower as int32) as int32) as int32))) <= 0;
                            ((-1 * to_integer((((lower as int32) as int32) as int32))) +
                                -to_integer(2147483648u64)) <= 0;
                        };
                    }
                    have ((-1 * to_integer((((value as int32) as int32) as int32))) + -to_integer(2147483648u64)) == ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + ((-1 * to_integer((((lower as int32) as int32) as int32))) + -to_integer(2147483648u64))) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute(((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + ((-1 * to_integer((((lower as int32) as int32) as int32))) + -to_integer(2147483648u64))), (0 + 0), ((-1 * to_integer((((value as int32) as int32) as int32))) + -to_integer(2147483648u64)), 0)) using {
                        ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower
                            as int32) as int32) as int32)) + ((-1 * to_integer((((lower as int32) as
                            int32) as int32))) + -to_integer(2147483648u64))) <= (0 + 0);
                        ((-1 * to_integer((((value as int32) as int32) as int32))) +
                            -to_integer(2147483648u64)) == ((-1 * to_integer((((value as int32) as
                            int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) +
                            ((-1 * to_integer((((lower as int32) as int32) as int32))) +
                            -to_integer(2147483648u64)));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer((((value as int32) as int32) as int32))) + -to_integer(2147483648u64)) == ((to_integer(((lower as int32) as int32)) + to_integer((-2147483648 as int32))) - (to_integer(((value as int32) as int32)) + to_integer((lower as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer(((lower as int32) as int32)) + to_integer((-2147483648 as int32))), (to_integer(((value as int32) as int32)) + to_integer((lower as int32))), ((-1 * to_integer((((value as int32) as int32) as int32))) + -to_integer(2147483648u64)))) using {
                    ((-1 * to_integer((((value as int32) as int32) as int32))) +
                        -to_integer(2147483648u64)) <= 0;
                    ((-1 * to_integer((((value as int32) as int32) as int32))) +
                        -to_integer(2147483648u64)) == ((to_integer(((lower as int32) as int32)) +
                        to_integer((-2147483648 as int32))) - (to_integer(((value as int32) as int32)) +
                        to_integer((lower as int32))));
                };
            }
            normalize() using {
                (to_integer(((lower as int32) as int32)) + to_integer((-2147483648 as int32))) <=
                    (to_integer(((value as int32) as int32)) + to_integer((lower as int32)));
            };
        }
        have to_integer((upper as int32)) <= to_integer((2147483647 as int32)) by {
            normalize() using {};
        }
        have (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) < (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))) by {
            have (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) < (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))) by {
                have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1) <= 0 by {
                    have to_integer((((value as int32) as int32) as int32)) < to_integer((((upper as int32) as int32) as int32)) by {
                        normalize() using {
                            ((value as int32) as int32) < ((upper as int32) as int32);
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + 1) <= to_integer((((upper as int32) as int32) as int32)) by {
                        apply(click::integer::lt_step_le(to_integer((((value as int32) as int32) as int32)), to_integer((((upper as int32) as int32) as int32)))) using {
                            to_integer((((value as int32) as int32) as int32)) < to_integer((((upper as
                                int32) as int32) as int32));
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1) == ((to_integer((((value as int32) as int32) as int32)) + 1) - to_integer((((upper as int32) as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer((((value as int32) as int32) as int32)) + 1), to_integer((((upper as int32) as int32) as int32)), (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1))) using {
                        (to_integer((((value as int32) as int32) as int32)) + 1) <= to_integer((((upper
                            as int32) as int32) as int32));
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper
                            as int32) as int32) as int32))) + 1) == ((to_integer((((value as int32) as
                            int32) as int32)) + 1) - to_integer((((upper as int32) as int32) as
                            int32)));
                    };
                }
                have (to_integer((((upper as int32) as int32) as int32)) + -2147483647) <= 0 by {
                    have (to_integer((((upper as int32) as int32) as int32)) + -2147483647) == (to_integer((upper as int32)) - to_integer((2147483647 as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((upper as int32)), to_integer((2147483647 as int32)), (to_integer((((upper as int32) as int32) as int32)) + -2147483647))) using {
                        to_integer((upper as int32)) <= to_integer((2147483647 as int32));
                        (to_integer((((upper as int32) as int32) as int32)) + -2147483647) ==
                            (to_integer((upper as int32)) - to_integer((2147483647 as int32)));
                    };
                }
                have (to_integer((((value as int32) as int32) as int32)) + -2147483646) <= 0 by {
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as int32) as int32)) + -2147483647)) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1), 0, (to_integer((((upper as int32) as int32) as int32)) + -2147483647), 0)) using {
                            (to_integer((((value as int32) as int32) as int32)) + (-1 *
                                to_integer((((upper as int32) as int32) as int32))) + 1) <= 0;
                            (to_integer((((upper as int32) as int32) as int32)) + -2147483647) <= 0;
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + -2147483646) == (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as int32) as int32)) + -2147483647)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as int32) as int32)) + -2147483647)), (0 + 0), (to_integer((((value as int32) as int32) as int32)) + -2147483646), 0)) using {
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((upper
                            as int32) as int32) as int32))) + 1 + (to_integer((((upper as int32) as
                            int32) as int32)) + -2147483647)) <= (0 + 0);
                        (to_integer((((value as int32) as int32) as int32)) + -2147483646) ==
                            (to_integer((((value as int32) as int32) as int32)) + (-1 *
                            to_integer((((upper as int32) as int32) as int32))) + 1 +
                            (to_integer((((upper as int32) as int32) as int32)) + -2147483647));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer((((value as int32) as int32) as int32)) + -2147483646) == ((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) - (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))), (to_integer((((value as int32) as int32) as int32)) + -2147483646))) using {
                    (to_integer((((value as int32) as int32) as int32)) + -2147483646) <= 0;
                    (to_integer((((value as int32) as int32) as int32)) + -2147483646) ==
                        ((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) -
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))));
                };
                apply(click::integer::step_le_lt((to_integer(((value as int32) as int32)) + to_integer((upper as int32))), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))))) using {
                    (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) <=
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)));
                };
            }
            normalize() using {
                (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) <
                    (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)));
            };
        }
        have -2147483648 <= to_integer((value as int32)) by {
            normalize() using {
                (to_integer(((lower as int32) as int32)) + to_integer((-2147483648 as int32))) <=
                    (to_integer(((value as int32) as int32)) + to_integer((lower as int32)));
            };
        }
        have to_integer((value as int32)) <= 2147483647 by {
            normalize() using {
                (to_integer(((lower as int32) as int32)) + to_integer((-2147483648 as int32))) <=
                    (to_integer(((value as int32) as int32)) + to_integer((lower as int32)));
            };
        }
        have -2147483648 <= to_integer((value as int32)) by {
            normalize() using {
                (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) <
                    (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)));
            };
        }
        have to_integer((value as int32)) <= 2147483646 by {
            have to_integer((value as int32)) <= 2147483646 by {
                have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1) <= 0 by {
                    have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) <= (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))) by {
                        apply(click::integer::lt_step_le((to_integer(((value as int32) as int32)) + to_integer((upper as int32))), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))))) using {
                            (to_integer(((value as int32) as int32)) + to_integer((upper as int32))) <
                                (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as
                                int32)));
                        };
                    }
                    have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1) == ((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) - (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1), (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32))), (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1))) using {
                        (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + 1) <=
                            (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as
                            int32)));
                        (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 *
                            (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as
                            int32)))) + 1) == ((to_integer(((value as int32) as int32)) +
                            to_integer((upper as int32)) + 1) - (to_integer(((upper as int32) as int32))
                            + to_integer((2147483647 as int32))));
                    };
                }
                have (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1) == (to_integer((value as int32)) - 2147483646) by {
                    normalize();
                }
                apply(click::integer::difference_le(to_integer((value as int32)), 2147483646, (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 * (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) + 1))) using {
                    (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 *
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) +
                        1) <= 0;
                    (to_integer(((value as int32) as int32)) + to_integer((upper as int32)) + (-1 *
                        (to_integer(((upper as int32) as int32)) + to_integer((2147483647 as int32)))) +
                        1) == (to_integer((value as int32)) - 2147483646);
                };
            }
            normalize() using {
                to_integer((value as int32)) <= 2147483646;
            };
        }
        have -2147483648 <= to_integer((value as int32)) by {
            normalize() using {
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483646;
            };
        }
        have to_integer((value as int32)) <= 2147483646 by {
            normalize() using {
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483646;
            };
        }
        have 1 <= to_integer((1 as int32)) by {
            normalize() using {};
        }
        have to_integer((1 as int32)) <= 1 by {
            normalize() using {};
        }
        have -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32))) by {
            have -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32))) by {
                have ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) == (-2147483648 - to_integer((value as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(-2147483648, to_integer((value as int32)), ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)))) using {
                        -2147483648 <= to_integer((value as int32));
                        ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) ==
                            (-2147483648 - to_integer((value as int32)));
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le(((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                        };
                    }
                    have ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute(((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)), 0)) using {
                        ((-1 * to_integer((value as int32))) + -to_integer(2147483648u64) + (let
                            integer_constant: Integer = -1; integer_constant)) <= (0 + 0);
                        ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == ((-1 *
                            to_integer((value as int32))) + -to_integer(2147483648u64) + (let
                            integer_constant: Integer = -1; integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == (-2147483648 - (to_integer((value as int32)) + to_integer((1 as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le(-2147483648, (to_integer((value as int32)) + to_integer((1 as int32))), ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)))) using {
                    ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) <= 0;
                    ((-1 * to_integer((value as int32))) + -to_integer(2147483649u64)) == (-2147483648 -
                        (to_integer((value as int32)) + to_integer((1 as int32))));
                };
            }
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32)));
            };
        }
        have (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647 by {
            have (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647 by {
                have (to_integer((value as int32)) + -2147483646) <= 0 by {
                    have (to_integer((value as int32)) + -2147483646) == (to_integer((value as int32)) - 2147483646) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((value as int32)), 2147483646, (to_integer((value as int32)) + -2147483646))) using {
                        to_integer((value as int32)) <= 2147483646;
                        (to_integer((value as int32)) + -2147483646) == (to_integer((value as int32)) -
                            2147483646);
                    };
                }
                have (to_integer((value as int32)) + -2147483646) == ((to_integer((value as int32)) + to_integer((1 as int32))) - 2147483647) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer((value as int32)) + to_integer((1 as int32))), 2147483647, (to_integer((value as int32)) + -2147483646))) using {
                    (to_integer((value as int32)) + -2147483646) <= 0;
                    (to_integer((value as int32)) + -2147483646) == ((to_integer((value as int32)) +
                        to_integer((1 as int32))) - 2147483647);
                };
            }
            normalize() using {
                (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647;
            };
        }
        have defined((value + 1)) by {
            known();
        }
        have to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as int32))) by {
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) + to_integer((1 as int32)));
                (to_integer((value as int32)) + to_integer((1 as int32))) <= 2147483647;
            };
        }
        have -2147483647 <= to_integer(((value + 1) as int32)) by {
            normalize() using {
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483646;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        have to_integer(((value + 1) as int32)) <= 2147483647 by {
            normalize() using {
                -2147483648 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483646;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        have -1 <= 0 by {
            normalize() using {
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        have (to_integer(((lower as int32) as int32)) + -1) <= (to_integer(((value as int32) as int32)) + 0) by {
            have defined(((value + 1) as int32)) by {
                known();
            }
            have defined((value + 1)) by {
                known();
            }
            have defined(old(((value + 1) as int32))) by {
                known();
            }
            have defined(old((value + 1))) by {
                known();
            }
            have (to_integer(((lower as int32) as int32)) + -1) <= (to_integer(((value as int32) as int32)) + 0) by {
                have ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32))) <= 0 by {
                    have to_integer((((lower as int32) as int32) as int32)) <= to_integer((((value as int32) as int32) as int32)) by {
                        normalize() using {
                            ((lower as int32) as int32) <= ((value as int32) as int32);
                        };
                    }
                    have ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32))) == (to_integer((((lower as int32) as int32) as int32)) - to_integer((((value as int32) as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((((lower as int32) as int32) as int32)), to_integer((((value as int32) as int32) as int32)), ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32))))) using {
                        to_integer((((lower as int32) as int32) as int32)) <= to_integer((((value as
                            int32) as int32) as int32));
                        ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower
                            as int32) as int32) as int32))) == (to_integer((((lower as int32) as int32)
                            as int32)) - to_integer((((value as int32) as int32) as int32)));
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + -1) <= 0 by {
                    have ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le(((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32))), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            ((-1 * to_integer((((value as int32) as int32) as int32))) +
                                to_integer((((lower as int32) as int32) as int32))) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    have ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + -1) == ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute(((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + -1), 0)) using {
                        ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower
                            as int32) as int32) as int32)) + (let integer_constant: Integer = -1;
                            integer_constant)) <= (0 + 0);
                        ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower
                            as int32) as int32) as int32)) + -1) == ((-1 * to_integer((((value as int32)
                            as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) +
                            (let integer_constant: Integer = -1; integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + -1) == ((to_integer(((lower as int32) as int32)) + -1) - (to_integer(((value as int32) as int32)) + 0)) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer(((lower as int32) as int32)) + -1), (to_integer(((value as int32) as int32)) + 0), ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as int32) as int32) as int32)) + -1))) using {
                    ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as
                        int32) as int32) as int32)) + -1) <= 0;
                    ((-1 * to_integer((((value as int32) as int32) as int32))) + to_integer((((lower as
                        int32) as int32) as int32)) + -1) == ((to_integer(((lower as int32) as int32)) +
                        -1) - (to_integer(((value as int32) as int32)) + 0));
                    defined(((value + 1) as int32));
                    defined((value + 1));
                    defined(old(((value + 1) as int32)));
                    defined(old((value + 1)));
                };
            }
            normalize() using {
                (to_integer(((lower as int32) as int32)) + -1) <= (to_integer(((value as int32) as
                    int32)) + 0);
            };
        }
        have (lower as int32) <= ((value + 1) as int32) by {
            have defined(((value + 1) as int32)) by {
                known();
            }
            have defined((value + 1)) by {
                known();
            }
            have defined(old(((value + 1) as int32))) by {
                known();
            }
            have defined(old((value + 1))) by {
                known();
            }
            have to_integer(((lower as int32) as int32)) <= to_integer((((value + 1) as int32) as int32)) by {
                have (to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as int32) as int32)) + 0))) <= 0 by {
                    have (to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as int32) as int32)) + 0))) == ((to_integer(((lower as int32) as int32)) + -1) - (to_integer(((value as int32) as int32)) + 0)) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer(((lower as int32) as int32)) + -1), (to_integer(((value as int32) as int32)) + 0), (to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as int32) as int32)) + 0))))) using {
                        (to_integer(((lower as int32) as int32)) + -1) <= (to_integer(((value as int32)
                            as int32)) + 0);
                        (to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as
                            int32) as int32)) + 0))) == ((to_integer(((lower as int32) as int32)) + -1)
                            - (to_integer(((value as int32) as int32)) + 0));
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) == 0 by {
                    have (to_integer(((value + 1) as int32)) - (to_integer((value as int32)) + to_integer((1 as int32)))) == 0 by {
                        apply(click::integer::equal_difference(to_integer(((value + 1) as int32)), (to_integer((value as int32)) + to_integer((1 as int32))))) using {
                            to_integer(((value + 1) as int32)) == (to_integer((value as int32)) +
                                to_integer((1 as int32)));
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    have ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) == (to_integer(((value + 1) as int32)) - (to_integer((value as int32)) + to_integer((1 as int32)))) by {
                        normalize();
                    }
                    apply(click::integer::equal_substitute((to_integer(((value + 1) as int32)) - (to_integer((value as int32)) + to_integer((1 as int32)))), 0, ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))), 0)) using {
                        (to_integer(((value + 1) as int32)) - (to_integer((value as int32)) +
                            to_integer((1 as int32)))) == 0;
                        ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) +
                            to_integer(((value + 1) as int32))) == (to_integer(((value + 1) as int32)) -
                            (to_integer((value as int32)) + to_integer((1 as int32))));
                        (let integer_value: Integer = 0; integer_value) == 0;
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))) <= 0 by {
                    have (((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) * -1) == (0 * -1) by {
                        apply(click::integer::equal_multiply(((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))), 0, -1)) using {
                            ((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) +
                                to_integer(((value + 1) as int32))) == 0;
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))) == 0 by {
                        have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))) == (((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) * -1) by {
                            normalize();
                        }
                        have (let integer_value: Integer = 0; integer_value) == (0 * -1) by {
                            normalize();
                        }
                        apply(click::integer::equal_substitute((((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as int32))) * -1), (0 * -1), (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))), 0)) using {
                            (((-1 * (to_integer((value as int32)) + to_integer((1 as int32)))) +
                                to_integer(((value + 1) as int32))) * -1) == (0 * -1);
                            (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 *
                                to_integer(((value + 1) as int32)))) == (((-1 * (to_integer((value as
                                int32)) + to_integer((1 as int32)))) + to_integer(((value + 1) as
                                int32))) * -1);
                            (let integer_value: Integer = 0; integer_value) == (0 * -1);
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    apply(click::integer::equal_le((to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))), 0)) using {
                        (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 *
                            to_integer(((value + 1) as int32)))) == 0;
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32))) + (to_integer(((lower as int32) as int32)) + -1) + (-1 * (to_integer(((value as int32) as int32)) + 0))) <= 0 by {
                    have (to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as int32) as int32)) + 0)) + (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32))))) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as int32) as int32)) + 0))), 0, (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32)))), 0)) using {
                            (to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as
                                int32) as int32)) + 0))) <= 0;
                            (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 *
                                to_integer(((value + 1) as int32)))) <= 0;
                            defined(((value + 1) as int32));
                            defined((value + 1));
                            defined(old(((value + 1) as int32)));
                            defined(old((value + 1)));
                        };
                    }
                    have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32))) + (to_integer(((lower as int32) as int32)) + -1) + (-1 * (to_integer(((value as int32) as int32)) + 0))) == (to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as int32) as int32)) + 0)) + (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32))))) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as int32) as int32)) + 0)) + (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32))))), (0 + 0), (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32))) + (to_integer(((lower as int32) as int32)) + -1) + (-1 * (to_integer(((value as int32) as int32)) + 0))), 0)) using {
                        (to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as
                            int32) as int32)) + 0)) + (to_integer((value as int32)) + to_integer((1 as
                            int32)) + (-1 * to_integer(((value + 1) as int32))))) <= (0 + 0);
                        (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 *
                            to_integer(((value + 1) as int32))) + (to_integer(((lower as int32) as
                            int32)) + -1) + (-1 * (to_integer(((value as int32) as int32)) + 0))) ==
                            (to_integer(((lower as int32) as int32)) + -1 + (-1 * (to_integer(((value as
                            int32) as int32)) + 0)) + (to_integer((value as int32)) + to_integer((1 as
                            int32)) + (-1 * to_integer(((value + 1) as int32)))));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                        defined(((value + 1) as int32));
                        defined((value + 1));
                        defined(old(((value + 1) as int32)));
                        defined(old((value + 1)));
                    };
                }
                have (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32))) + (to_integer(((lower as int32) as int32)) + -1) + (-1 * (to_integer(((value as int32) as int32)) + 0))) == (to_integer(((lower as int32) as int32)) - to_integer((((value + 1) as int32) as int32))) by {
                    normalize();
                }
                apply(click::integer::difference_le(to_integer(((lower as int32) as int32)), to_integer((((value + 1) as int32) as int32)), (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value + 1) as int32))) + (to_integer(((lower as int32) as int32)) + -1) + (-1 * (to_integer(((value as int32) as int32)) + 0))))) using {
                    (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value
                        + 1) as int32))) + (to_integer(((lower as int32) as int32)) + -1) + (-1 *
                        (to_integer(((value as int32) as int32)) + 0))) <= 0;
                    (to_integer((value as int32)) + to_integer((1 as int32)) + (-1 * to_integer(((value
                        + 1) as int32))) + (to_integer(((lower as int32) as int32)) + -1) + (-1 *
                        (to_integer(((value as int32) as int32)) + 0))) == (to_integer(((lower as int32)
                        as int32)) - to_integer((((value + 1) as int32) as int32)));
                    defined(((value + 1) as int32));
                    defined((value + 1));
                    defined(old(((value + 1) as int32)));
                    defined(old((value + 1)));
                };
            }
            normalize() using {
                to_integer(((lower as int32) as int32)) <= to_integer((((value + 1) as int32) as
                    int32));
            };
        }
        have to_integer(lower) <= to_integer((value + 1)) by {
            normalize() using {
                (lower as int32) <= ((value + 1) as int32);
                to_integer(((value + 1) as int32)) == (to_integer((value as int32)) + to_integer((1 as
                    int32)));
            };
        }
        known();
    }
}

theorem int32_positive_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value by {
        normalize() using { 0 < value; };
    }
}

theorem int32_increment_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(value + 1) by {
        have -2147483648 <= to_integer(value) by normalize();
        have to_integer(value) + 1 <= 2147483647 by {
            apply(integer::lt_step_le(to_integer(value), 2147483647)) using { to_integer(value) < 2147483647; };
        }
        have -2147483648 + 0 <= to_integer(value) + 1 by {
            apply(integer::add_le(-2147483648, to_integer(value), 0, 1)) using { -2147483648 <= to_integer(value); 0 <= 1; };
        }
        have -2147483648 == -2147483648 + 0 by normalize();
        have -2147483648 <= to_integer(value) + 1 by {
            apply(integer::le_substitute(-2147483648 + 0, to_integer(value) + 1, -2147483648, to_integer(value) + 1)) using {
                -2147483648 + 0 <= to_integer(value) + 1;
                -2147483648 == -2147483648 + 0;
                to_integer(value) + 1 == to_integer(value) + 1;
            };
        }
        known();
    }
}

theorem int32_nonnegative_add_within_max_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires to_integer(value) <= to_integer(2147483647 - amount);

    ensures defined(value + amount) by {
        have -2147483648 <= (2147483647 - to_integer(amount)) by {
            have -2147483648 <= (2147483647 - to_integer(amount)) by {
                have (to_integer(amount) + -2147483647) <= 0 by {
                    have to_integer(amount) <= 2147483647 by {
                        normalize();
                    }
                    have (to_integer(amount) + -2147483647) == (to_integer(amount) - 2147483647) by {
                        normalize();
                    }
                    apply(integer::le_difference(to_integer(amount), 2147483647, (to_integer(amount) + -2147483647))) using {
                        to_integer(amount) <= 2147483647;
                        (to_integer(amount) + -2147483647) == (to_integer(amount) - 2147483647);
                    };
                }
                have (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant) <= 0 by {
                    normalize();
                }
                have (to_integer(amount) + -to_integer(4294967295u64)) <= 0 by {
                    have (to_integer(amount) + -2147483647 + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)) <= (0 + 0) by {
                        apply(integer::add_le((to_integer(amount) + -2147483647), 0, (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant), 0)) using {
                            (to_integer(amount) + -2147483647) <= 0;
                            (let integer_constant: Integer = -to_integer(2147483648u64);
                                integer_constant) <= 0;
                        };
                    }
                    have (to_integer(amount) + -to_integer(4294967295u64)) == (to_integer(amount) + -2147483647 + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute((to_integer(amount) + -2147483647 + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)), (0 + 0), (to_integer(amount) + -to_integer(4294967295u64)), 0)) using {
                        (to_integer(amount) + -2147483647 + (let integer_constant: Integer =
                            -to_integer(2147483648u64); integer_constant)) <= (0 + 0);
                        (to_integer(amount) + -to_integer(4294967295u64)) == (to_integer(amount) +
                            -2147483647 + (let integer_constant: Integer = -to_integer(2147483648u64);
                            integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer(amount) + -to_integer(4294967295u64)) == (-2147483648 - (2147483647 - to_integer(amount))) by {
                    normalize();
                }
                apply(integer::difference_le(-2147483648, (2147483647 - to_integer(amount)), (to_integer(amount) + -to_integer(4294967295u64)))) using {
                    (to_integer(amount) + -to_integer(4294967295u64)) <= 0;
                    (to_integer(amount) + -to_integer(4294967295u64)) == (-2147483648 - (2147483647 -
                        to_integer(amount)));
                };
            }
            normalize() using {
                -2147483648 <= (2147483647 - to_integer(amount));
            };
        }
        have (2147483647 - to_integer(amount)) <= 2147483647 by {
            have (2147483647 - to_integer(amount)) <= 2147483647 by {
                have (-1 * to_integer(amount)) <= 0 by {
                    have (-1 * to_integer(amount)) == (0 - to_integer(amount)) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer(amount), (-1 * to_integer(amount)))) using {
                        0 <= to_integer(amount);
                        (-1 * to_integer(amount)) == (0 - to_integer(amount));
                    };
                }
                have (-1 * to_integer(amount)) == ((2147483647 - to_integer(amount)) - 2147483647) by {
                    normalize();
                }
                apply(integer::difference_le((2147483647 - to_integer(amount)), 2147483647, (-1 * to_integer(amount)))) using {
                    (-1 * to_integer(amount)) <= 0;
                    (-1 * to_integer(amount)) == ((2147483647 - to_integer(amount)) - 2147483647);
                };
            }
            normalize() using {
                (2147483647 - to_integer(amount)) <= 2147483647;
            };
        }
        have to_integer((2147483647 - amount)) == (2147483647 - to_integer(amount)) by {
            normalize() using {
                -2147483648 <= (2147483647 - to_integer(amount));
                (2147483647 - to_integer(amount)) <= 2147483647;
            };
        }
        have -2147483648 <= (to_integer(value) + to_integer(amount)) by {
            have -2147483648 <= (to_integer(value) + to_integer(amount)) by {
                have (-1 * to_integer(amount)) <= 0 by {
                    have (-1 * to_integer(amount)) == (0 - to_integer(amount)) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer(amount), (-1 * to_integer(amount)))) using {
                        0 <= to_integer(amount);
                        (-1 * to_integer(amount)) == (0 - to_integer(amount));
                    };
                }
                have ((-1 * to_integer(value)) + -to_integer(2147483648u64)) <= 0 by {
                    have -2147483648 <= to_integer(value) by {
                        normalize();
                    }
                    have ((-1 * to_integer(value)) + -to_integer(2147483648u64)) == (-2147483648 - to_integer(value)) by {
                        normalize();
                    }
                    apply(integer::le_difference(-2147483648, to_integer(value), ((-1 * to_integer(value)) + -to_integer(2147483648u64)))) using {
                        -2147483648 <= to_integer(value);
                        ((-1 * to_integer(value)) + -to_integer(2147483648u64)) == (-2147483648 -
                            to_integer(value));
                    };
                }
                have ((-1 * to_integer(amount)) + (-1 * to_integer(value)) + -to_integer(2147483648u64)) <= 0 by {
                    have ((-1 * to_integer(amount)) + ((-1 * to_integer(value)) + -to_integer(2147483648u64))) <= (0 + 0) by {
                        apply(integer::add_le((-1 * to_integer(amount)), 0, ((-1 * to_integer(value)) + -to_integer(2147483648u64)), 0)) using {
                            (-1 * to_integer(amount)) <= 0;
                            ((-1 * to_integer(value)) + -to_integer(2147483648u64)) <= 0;
                        };
                    }
                    have ((-1 * to_integer(amount)) + (-1 * to_integer(value)) + -to_integer(2147483648u64)) == ((-1 * to_integer(amount)) + ((-1 * to_integer(value)) + -to_integer(2147483648u64))) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute(((-1 * to_integer(amount)) + ((-1 * to_integer(value)) + -to_integer(2147483648u64))), (0 + 0), ((-1 * to_integer(amount)) + (-1 * to_integer(value)) + -to_integer(2147483648u64)), 0)) using {
                        ((-1 * to_integer(amount)) + ((-1 * to_integer(value)) +
                            -to_integer(2147483648u64))) <= (0 + 0);
                        ((-1 * to_integer(amount)) + (-1 * to_integer(value)) +
                            -to_integer(2147483648u64)) == ((-1 * to_integer(amount)) + ((-1 *
                            to_integer(value)) + -to_integer(2147483648u64)));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer(amount)) + (-1 * to_integer(value)) + -to_integer(2147483648u64)) == (-2147483648 - (to_integer(value) + to_integer(amount))) by {
                    normalize();
                }
                apply(integer::difference_le(-2147483648, (to_integer(value) + to_integer(amount)), ((-1 * to_integer(amount)) + (-1 * to_integer(value)) + -to_integer(2147483648u64)))) using {
                    ((-1 * to_integer(amount)) + (-1 * to_integer(value)) + -to_integer(2147483648u64))
                        <= 0;
                    ((-1 * to_integer(amount)) + (-1 * to_integer(value)) + -to_integer(2147483648u64))
                        == (-2147483648 - (to_integer(value) + to_integer(amount)));
                };
            }
            normalize() using {
                -2147483648 <= (to_integer(value) + to_integer(amount));
            };
        }
        have (to_integer(value) + to_integer(amount)) <= 2147483647 by {
            have to_integer(value) <= 2147483647 - to_integer(amount) by {
                rewrite(2147483647 - to_integer(amount), to_integer(2147483647 - amount));
                known();
            }
            have to_integer(value) + to_integer(amount) <= (2147483647 - to_integer(amount)) + to_integer(amount) by {
                apply(integer::add_le(to_integer(value), 2147483647 - to_integer(amount), to_integer(amount), to_integer(amount))) using { to_integer(value) <= 2147483647 - to_integer(amount); to_integer(amount) <= to_integer(amount); };
            }
            have 2147483647 == (2147483647 - to_integer(amount)) + to_integer(amount) by normalize();
            apply(integer::le_substitute(to_integer(value) + to_integer(amount), (2147483647 - to_integer(amount)) + to_integer(amount), to_integer(value) + to_integer(amount), 2147483647)) using {
                to_integer(value) + to_integer(amount) <= (2147483647 - to_integer(amount)) + to_integer(amount);
                to_integer(value) + to_integer(amount) == to_integer(value) + to_integer(amount);
                2147483647 == (2147483647 - to_integer(amount)) + to_integer(amount);
            };
        }
        known();
    }
}

theorem int32_nonnegative_subtract_within_value_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires amount <= value;

    ensures defined(value - amount) by {
        have to_integer(value) <= 2147483647 by {
            normalize();
        }
        have -2147483648 <= (to_integer(value) - to_integer(amount)) by {
            have -2147483648 <= (to_integer(value) - to_integer(amount)) by {
                have (to_integer((amount as int32)) + (-1 * to_integer((value as int32)))) <= 0 by {
                    have to_integer((amount as int32)) <= to_integer((value as int32)) by {
                        normalize() using {
                            amount <= value;
                        };
                    }
                    have (to_integer((amount as int32)) + (-1 * to_integer((value as int32)))) == (to_integer((amount as int32)) - to_integer((value as int32))) by {
                        normalize();
                    }
                    apply(integer::le_difference(to_integer((amount as int32)), to_integer((value as int32)), (to_integer((amount as int32)) + (-1 * to_integer((value as int32)))))) using {
                        to_integer((amount as int32)) <= to_integer((value as int32));
                        (to_integer((amount as int32)) + (-1 * to_integer((value as int32)))) ==
                            (to_integer((amount as int32)) - to_integer((value as int32)));
                    };
                }
                have (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant) <= 0 by {
                    normalize();
                }
                have (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) <= 0 by {
                    have (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)) <= (0 + 0) by {
                        apply(integer::add_le((to_integer((amount as int32)) + (-1 * to_integer((value as int32)))), 0, (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant), 0)) using {
                            (to_integer((amount as int32)) + (-1 * to_integer((value as int32)))) <= 0;
                            (let integer_constant: Integer = -to_integer(2147483648u64);
                                integer_constant) <= 0;
                        };
                    }
                    have (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) == (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute((to_integer((amount as int32)) + (-1 * to_integer((value as int32))) + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)), (0 + 0), (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) + -to_integer(2147483648u64)), 0)) using {
                        (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) + (let
                            integer_constant: Integer = -to_integer(2147483648u64); integer_constant))
                            <= (0 + 0);
                        (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) +
                            -to_integer(2147483648u64)) == (to_integer((amount as int32)) + (-1 *
                            to_integer((value as int32))) + (let integer_constant: Integer =
                            -to_integer(2147483648u64); integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) + -to_integer(2147483648u64)) == (-2147483648 - (to_integer(value) - to_integer(amount))) by {
                    normalize();
                }
                apply(integer::difference_le(-2147483648, (to_integer(value) - to_integer(amount)), (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) + -to_integer(2147483648u64)))) using {
                    (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) +
                        -to_integer(2147483648u64)) <= 0;
                    (to_integer((amount as int32)) + (-1 * to_integer((value as int32))) +
                        -to_integer(2147483648u64)) == (-2147483648 - (to_integer(value) -
                        to_integer(amount)));
                };
            }
            normalize() using {
                -2147483648 <= (to_integer(value) - to_integer(amount));
            };
        }
        have (to_integer(value) - to_integer(amount)) <= 2147483647 by {
            have (to_integer(value) - to_integer(amount)) <= 2147483647 by {
                have (-1 * to_integer((amount as int32))) <= 0 by {
                    have 0 <= to_integer((amount as int32)) by {
                        normalize() using {
                            0 <= amount;
                        };
                    }
                    have (-1 * to_integer((amount as int32))) == (0 - to_integer((amount as int32))) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer((amount as int32)), (-1 * to_integer((amount as int32))))) using {
                        0 <= to_integer((amount as int32));
                        (-1 * to_integer((amount as int32))) == (0 - to_integer((amount as int32)));
                    };
                }
                have (to_integer(value) + -2147483647) <= 0 by {
                    have (to_integer(value) + -2147483647) == (to_integer(value) - 2147483647) by {
                        normalize();
                    }
                    apply(integer::le_difference(to_integer(value), 2147483647, (to_integer(value) + -2147483647))) using {
                        to_integer(value) <= 2147483647;
                        (to_integer(value) + -2147483647) == (to_integer(value) - 2147483647);
                    };
                }
                have ((-1 * to_integer((amount as int32))) + to_integer(value) + -2147483647) <= 0 by {
                    have ((-1 * to_integer((amount as int32))) + (to_integer(value) + -2147483647)) <= (0 + 0) by {
                        apply(integer::add_le((-1 * to_integer((amount as int32))), 0, (to_integer(value) + -2147483647), 0)) using {
                            (-1 * to_integer((amount as int32))) <= 0;
                            (to_integer(value) + -2147483647) <= 0;
                        };
                    }
                    have ((-1 * to_integer((amount as int32))) + to_integer(value) + -2147483647) == ((-1 * to_integer((amount as int32))) + (to_integer(value) + -2147483647)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute(((-1 * to_integer((amount as int32))) + (to_integer(value) + -2147483647)), (0 + 0), ((-1 * to_integer((amount as int32))) + to_integer(value) + -2147483647), 0)) using {
                        ((-1 * to_integer((amount as int32))) + (to_integer(value) + -2147483647)) <= (0
                            + 0);
                        ((-1 * to_integer((amount as int32))) + to_integer(value) + -2147483647) == ((-1
                            * to_integer((amount as int32))) + (to_integer(value) + -2147483647));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer((amount as int32))) + to_integer(value) + -2147483647) == ((to_integer(value) - to_integer(amount)) - 2147483647) by {
                    normalize();
                }
                apply(integer::difference_le((to_integer(value) - to_integer(amount)), 2147483647, ((-1 * to_integer((amount as int32))) + to_integer(value) + -2147483647))) using {
                    ((-1 * to_integer((amount as int32))) + to_integer(value) + -2147483647) <= 0;
                    ((-1 * to_integer((amount as int32))) + to_integer(value) + -2147483647) ==
                        ((to_integer(value) - to_integer(amount)) - 2147483647);
                };
            }
            normalize() using {
                (to_integer(value) - to_integer(amount)) <= 2147483647;
            };
        }
        known();
    }
}

theorem int32_positive_predecessor_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= to_integer(value - 1) by {
        have 1 <= to_integer((value as int32)) by {
            normalize() using {
                ((0 as int32) as int32) < ((value as int32) as int32);
            };
        }
        have to_integer((value as int32)) <= 2147483647 by {
            normalize() using {
                ((0 as int32) as int32) < ((value as int32) as int32);
            };
        }
        have 1 <= to_integer((1 as int32)) by {
            normalize() using {};
        }
        have to_integer((1 as int32)) <= 1 by {
            normalize() using {};
        }
        have -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32))) by {
            have -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32))) by {
                have ((-1 * to_integer((value as int32))) + 1) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + 1) == (1 - to_integer((value as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(1, to_integer((value as int32)), ((-1 * to_integer((value as int32))) + 1))) using {
                        1 <= to_integer((value as int32));
                        ((-1 * to_integer((value as int32))) + 1) == (1 - to_integer((value as int32)));
                    };
                }
                have (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant) <= 0 by {
                    normalize();
                }
                have ((-1 * to_integer((value as int32))) + -2147483647) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + 1 + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le(((-1 * to_integer((value as int32))) + 1), 0, (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant), 0)) using {
                            ((-1 * to_integer((value as int32))) + 1) <= 0;
                            (let integer_constant: Integer = -to_integer(2147483648u64);
                                integer_constant) <= 0;
                        };
                    }
                    have ((-1 * to_integer((value as int32))) + -2147483647) == ((-1 * to_integer((value as int32))) + 1 + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute(((-1 * to_integer((value as int32))) + 1 + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)), (0 + 0), ((-1 * to_integer((value as int32))) + -2147483647), 0)) using {
                        ((-1 * to_integer((value as int32))) + 1 + (let integer_constant: Integer =
                            -to_integer(2147483648u64); integer_constant)) <= (0 + 0);
                        ((-1 * to_integer((value as int32))) + -2147483647) == ((-1 * to_integer((value
                            as int32))) + 1 + (let integer_constant: Integer =
                            -to_integer(2147483648u64); integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer((value as int32))) + -2147483647) == (-2147483648 - (to_integer((value as int32)) - to_integer((1 as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le(-2147483648, (to_integer((value as int32)) - to_integer((1 as int32))), ((-1 * to_integer((value as int32))) + -2147483647))) using {
                    ((-1 * to_integer((value as int32))) + -2147483647) <= 0;
                    ((-1 * to_integer((value as int32))) + -2147483647) == (-2147483648 -
                        (to_integer((value as int32)) - to_integer((1 as int32))));
                };
            }
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32)));
            };
        }
        have (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647 by {
            have (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647 by {
                have (to_integer((value as int32)) + -2147483647) <= 0 by {
                    have (to_integer((value as int32)) + -2147483647) == (to_integer((value as int32)) - 2147483647) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((value as int32)), 2147483647, (to_integer((value as int32)) + -2147483647))) using {
                        to_integer((value as int32)) <= 2147483647;
                        (to_integer((value as int32)) + -2147483647) == (to_integer((value as int32)) -
                            2147483647);
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have (to_integer((value as int32)) + -to_integer(2147483648u64)) <= 0 by {
                    have (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer((value as int32)) + -2147483647), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            (to_integer((value as int32)) + -2147483647) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                        };
                    }
                    have (to_integer((value as int32)) + -to_integer(2147483648u64)) == (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), (to_integer((value as int32)) + -to_integer(2147483648u64)), 0)) using {
                        (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer =
                            -1; integer_constant)) <= (0 + 0);
                        (to_integer((value as int32)) + -to_integer(2147483648u64)) ==
                            (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer
                            = -1; integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer((value as int32)) + -to_integer(2147483648u64)) == ((to_integer((value as int32)) - to_integer((1 as int32))) - 2147483647) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer((value as int32)) - to_integer((1 as int32))), 2147483647, (to_integer((value as int32)) + -to_integer(2147483648u64)))) using {
                    (to_integer((value as int32)) + -to_integer(2147483648u64)) <= 0;
                    (to_integer((value as int32)) + -to_integer(2147483648u64)) == ((to_integer((value
                        as int32)) - to_integer((1 as int32))) - 2147483647);
                };
            }
            normalize() using {
                (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647;
            };
        }
        have defined((value - 1)) by {
            known();
        }
        have to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as int32))) by {
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32)));
                (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647;
            };
        }
        have 0 <= to_integer(((value - 1) as int32)) by {
            normalize() using {
                1 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                1 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        have to_integer(((value - 1) as int32)) <= 2147483646 by {
            normalize() using {
                1 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                1 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        have (0 as int32) <= ((value - 1) as int32) by {
            normalize() using {
                ((0 as int32) as int32) < ((value as int32) as int32);
                0 <= to_integer(((value - 1) as int32));
                to_integer(((value - 1) as int32)) <= 2147483646;
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        have 0 <= to_integer((value - 1)) by {
            normalize() using {
                (0 as int32) <= ((value - 1) as int32);
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        known();
    }
}

theorem int32_positive_predecessor_strictly_decreases(value: int32) {
    requires 0 < value;

    ensures to_integer(value - 1) < to_integer(value) by {
        have 1 <= to_integer((value as int32)) by {
            normalize() using {
                ((0 as int32) as int32) < ((value as int32) as int32);
            };
        }
        have to_integer((value as int32)) <= 2147483647 by {
            normalize() using {
                ((0 as int32) as int32) < ((value as int32) as int32);
            };
        }
        have 1 <= to_integer((1 as int32)) by {
            normalize() using {};
        }
        have to_integer((1 as int32)) <= 1 by {
            normalize() using {};
        }
        have -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32))) by {
            have -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32))) by {
                have ((-1 * to_integer((value as int32))) + 1) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + 1) == (1 - to_integer((value as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(1, to_integer((value as int32)), ((-1 * to_integer((value as int32))) + 1))) using {
                        1 <= to_integer((value as int32));
                        ((-1 * to_integer((value as int32))) + 1) == (1 - to_integer((value as int32)));
                    };
                }
                have (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant) <= 0 by {
                    normalize();
                }
                have ((-1 * to_integer((value as int32))) + -2147483647) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + 1 + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le(((-1 * to_integer((value as int32))) + 1), 0, (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant), 0)) using {
                            ((-1 * to_integer((value as int32))) + 1) <= 0;
                            (let integer_constant: Integer = -to_integer(2147483648u64);
                                integer_constant) <= 0;
                        };
                    }
                    have ((-1 * to_integer((value as int32))) + -2147483647) == ((-1 * to_integer((value as int32))) + 1 + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute(((-1 * to_integer((value as int32))) + 1 + (let integer_constant: Integer = -to_integer(2147483648u64); integer_constant)), (0 + 0), ((-1 * to_integer((value as int32))) + -2147483647), 0)) using {
                        ((-1 * to_integer((value as int32))) + 1 + (let integer_constant: Integer =
                            -to_integer(2147483648u64); integer_constant)) <= (0 + 0);
                        ((-1 * to_integer((value as int32))) + -2147483647) == ((-1 * to_integer((value
                            as int32))) + 1 + (let integer_constant: Integer =
                            -to_integer(2147483648u64); integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer((value as int32))) + -2147483647) == (-2147483648 - (to_integer((value as int32)) - to_integer((1 as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le(-2147483648, (to_integer((value as int32)) - to_integer((1 as int32))), ((-1 * to_integer((value as int32))) + -2147483647))) using {
                    ((-1 * to_integer((value as int32))) + -2147483647) <= 0;
                    ((-1 * to_integer((value as int32))) + -2147483647) == (-2147483648 -
                        (to_integer((value as int32)) - to_integer((1 as int32))));
                };
            }
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32)));
            };
        }
        have (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647 by {
            have (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647 by {
                have (to_integer((value as int32)) + -2147483647) <= 0 by {
                    have (to_integer((value as int32)) + -2147483647) == (to_integer((value as int32)) - 2147483647) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((value as int32)), 2147483647, (to_integer((value as int32)) + -2147483647))) using {
                        to_integer((value as int32)) <= 2147483647;
                        (to_integer((value as int32)) + -2147483647) == (to_integer((value as int32)) -
                            2147483647);
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have (to_integer((value as int32)) + -to_integer(2147483648u64)) <= 0 by {
                    have (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer((value as int32)) + -2147483647), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            (to_integer((value as int32)) + -2147483647) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                        };
                    }
                    have (to_integer((value as int32)) + -to_integer(2147483648u64)) == (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), (to_integer((value as int32)) + -to_integer(2147483648u64)), 0)) using {
                        (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer =
                            -1; integer_constant)) <= (0 + 0);
                        (to_integer((value as int32)) + -to_integer(2147483648u64)) ==
                            (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer
                            = -1; integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer((value as int32)) + -to_integer(2147483648u64)) == ((to_integer((value as int32)) - to_integer((1 as int32))) - 2147483647) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer((value as int32)) - to_integer((1 as int32))), 2147483647, (to_integer((value as int32)) + -to_integer(2147483648u64)))) using {
                    (to_integer((value as int32)) + -to_integer(2147483648u64)) <= 0;
                    (to_integer((value as int32)) + -to_integer(2147483648u64)) == ((to_integer((value
                        as int32)) - to_integer((1 as int32))) - 2147483647);
                };
            }
            normalize() using {
                (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647;
            };
        }
        have defined((value - 1)) by {
            known();
        }
        have to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as int32))) by {
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32)));
                (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647;
            };
        }
        have 0 <= to_integer(((value - 1) as int32)) by {
            normalize() using {
                1 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                1 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        have to_integer(((value - 1) as int32)) <= 2147483646 by {
            normalize() using {
                1 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                1 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        have 0 <= 0 by {
            normalize() using {
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        have ((value - 1) as int32) < (value as int32) by {
            have defined(((value - 1) as int32)) by {
                known();
            }
            have defined((value - 1)) by {
                known();
            }
            have defined(old(((value - 1) as int32))) by {
                known();
            }
            have defined(old((value - 1))) by {
                known();
            }
            have to_integer((((value - 1) as int32) as int32)) < to_integer(((value as int32) as int32)) by {
                have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))) == 0 by {
                    have (to_integer(((value - 1) as int32)) - (to_integer((value as int32)) - to_integer((1 as int32)))) == 0 by {
                        apply(click::integer::equal_difference(to_integer(((value - 1) as int32)), (to_integer((value as int32)) - to_integer((1 as int32))))) using {
                            to_integer(((value - 1) as int32)) == (to_integer((value as int32)) -
                                to_integer((1 as int32)));
                            defined(((value - 1) as int32));
                            defined((value - 1));
                            defined(old(((value - 1) as int32)));
                            defined(old((value - 1)));
                        };
                    }
                    have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))) == (to_integer(((value - 1) as int32)) - (to_integer((value as int32)) - to_integer((1 as int32)))) by {
                        normalize();
                    }
                    apply(click::integer::equal_substitute((to_integer(((value - 1) as int32)) - (to_integer((value as int32)) - to_integer((1 as int32)))), 0, ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))), 0)) using {
                        (to_integer(((value - 1) as int32)) - (to_integer((value as int32)) -
                            to_integer((1 as int32)))) == 0;
                        ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                            to_integer(((value - 1) as int32))) == (to_integer(((value - 1) as int32)) -
                            (to_integer((value as int32)) - to_integer((1 as int32))));
                        (let integer_value: Integer = 0; integer_value) == 0;
                        defined(((value - 1) as int32));
                        defined((value - 1));
                        defined(old(((value - 1) as int32)));
                        defined(old((value - 1)));
                    };
                }
                have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))) <= 0 by {
                    apply(click::integer::equal_le(((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))), 0)) using {
                        ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                            to_integer(((value - 1) as int32))) == 0;
                        defined(((value - 1) as int32));
                        defined((value - 1));
                        defined(old(((value - 1) as int32)));
                        defined(old((value - 1)));
                    };
                }
                have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))) == ((to_integer((((value - 1) as int32) as int32)) + 1) - to_integer(((value as int32) as int32))) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer((((value - 1) as int32) as int32)) + 1), to_integer(((value as int32) as int32)), ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))))) using {
                    ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                        to_integer(((value - 1) as int32))) <= 0;
                    ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                        to_integer(((value - 1) as int32))) == ((to_integer((((value - 1) as int32) as
                        int32)) + 1) - to_integer(((value as int32) as int32)));
                    defined(((value - 1) as int32));
                    defined((value - 1));
                    defined(old(((value - 1) as int32)));
                    defined(old((value - 1)));
                };
                apply(click::integer::step_le_lt(to_integer((((value - 1) as int32) as int32)), to_integer(((value as int32) as int32)))) using {
                    (to_integer((((value - 1) as int32) as int32)) + 1) <= to_integer(((value as int32)
                        as int32));
                    defined(((value - 1) as int32));
                    defined((value - 1));
                    defined(old(((value - 1) as int32)));
                    defined(old((value - 1)));
                };
            }
            normalize() using {
                to_integer((((value - 1) as int32) as int32)) < to_integer(((value as int32) as int32));
            };
        }
        have to_integer((value - 1)) < to_integer(value) by {
            normalize() using {
                ((value - 1) as int32) < (value as int32);
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        known();
    }
}

theorem uint32_positive_predecessor_strictly_decreases(value: uint32) {
    requires 0u32 < value;

    ensures to_integer(value - 1u32) < to_integer(value) by {
        have 0 < to_integer(value) by {
            known();
        }
        have 0 <= (to_integer(value) - 1) by {
            have 0 <= (to_integer(value) - 1) by {
                have ((-1 * to_integer(value)) + 1) <= 0 by {
                    have (0 + 1) <= to_integer(value) by {
                        apply(integer::lt_step_le(0, to_integer(value))) using {
                            0 < to_integer(value);
                        };
                    }
                    have ((-1 * to_integer(value)) + 1) == ((0 + 1) - to_integer(value)) by {
                        normalize();
                    }
                    apply(integer::le_difference((0 + 1), to_integer(value), ((-1 * to_integer(value)) + 1))) using {
                        (0 + 1) <= to_integer(value);
                        ((-1 * to_integer(value)) + 1) == ((0 + 1) - to_integer(value));
                    };
                }
                have ((-1 * to_integer(value)) + 1) == (0 - (to_integer(value) - 1)) by {
                    normalize();
                }
                apply(integer::difference_le(0, (to_integer(value) - 1), ((-1 * to_integer(value)) + 1))) using {
                    ((-1 * to_integer(value)) + 1) <= 0;
                    ((-1 * to_integer(value)) + 1) == (0 - (to_integer(value) - 1));
                };
            }
            normalize() using {
                0 <= (to_integer(value) - 1);
            };
        }
        have (to_integer(value) - 1) <= 4294967295 by {
            have (to_integer(value) - 1) <= 4294967295 by {
                have (to_integer(value) + -to_integer(4294967295u64)) <= 0 by {
                    have to_integer(value) <= 4294967295 by {
                        normalize();
                    }
                    have (to_integer(value) + -to_integer(4294967295u64)) == (to_integer(value) - 4294967295) by {
                        normalize();
                    }
                    apply(integer::le_difference(to_integer(value), 4294967295, (to_integer(value) + -to_integer(4294967295u64)))) using {
                        to_integer(value) <= 4294967295;
                        (to_integer(value) + -to_integer(4294967295u64)) == (to_integer(value) -
                            4294967295);
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have (to_integer(value) + -to_integer(4294967296u64)) <= 0 by {
                    have (to_integer(value) + -to_integer(4294967295u64) + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(integer::add_le((to_integer(value) + -to_integer(4294967295u64)), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            (to_integer(value) + -to_integer(4294967295u64)) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                        };
                    }
                    have (to_integer(value) + -to_integer(4294967296u64)) == (to_integer(value) + -to_integer(4294967295u64) + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute((to_integer(value) + -to_integer(4294967295u64) + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), (to_integer(value) + -to_integer(4294967296u64)), 0)) using {
                        (to_integer(value) + -to_integer(4294967295u64) + (let integer_constant: Integer
                            = -1; integer_constant)) <= (0 + 0);
                        (to_integer(value) + -to_integer(4294967296u64)) == (to_integer(value) +
                            -to_integer(4294967295u64) + (let integer_constant: Integer = -1;
                            integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer(value) + -to_integer(4294967296u64)) == ((to_integer(value) - 1) - 4294967295) by {
                    normalize();
                }
                apply(integer::difference_le((to_integer(value) - 1), 4294967295, (to_integer(value) + -to_integer(4294967296u64)))) using {
                    (to_integer(value) + -to_integer(4294967296u64)) <= 0;
                    (to_integer(value) + -to_integer(4294967296u64)) == ((to_integer(value) - 1) -
                        4294967295);
                };
            }
            normalize() using {
                (to_integer(value) - 1) <= 4294967295;
            };
        }
        have to_integer((value - 1u32)) == (to_integer(value) - 1) by {
            normalize() using {
                0 <= (to_integer(value) - 1);
                (to_integer(value) - 1) <= 4294967295;
            };
        }
        have to_integer((value - 1u32)) < to_integer(value) by {
            have ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))) == 0 by {
                have (to_integer((value - 1u32)) - (to_integer(value) - 1)) == 0 by {
                    apply(integer::equal_difference(to_integer((value - 1u32)), (to_integer(value) - 1))) using {
                        to_integer((value - 1u32)) == (to_integer(value) - 1);
                    };
                }
                have ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))) == (to_integer((value - 1u32)) - (to_integer(value) - 1)) by {
                    normalize();
                }
                apply(integer::equal_substitute((to_integer((value - 1u32)) - (to_integer(value) - 1)), 0, ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))), 0)) using {
                    (to_integer((value - 1u32)) - (to_integer(value) - 1)) == 0;
                    ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))) == (to_integer((value
                        - 1u32)) - (to_integer(value) - 1));
                    (let integer_value: Integer = 0; integer_value) == 0;
                };
            }
            have ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))) <= 0 by {
                apply(integer::equal_le(((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))), 0)) using {
                    ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))) == 0;
                };
            }
            have ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))) == ((to_integer((value - 1u32)) + 1) - to_integer(value)) by {
                normalize();
            }
            apply(integer::difference_le((to_integer((value - 1u32)) + 1), to_integer(value), ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))))) using {
                ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))) <= 0;
                ((-1 * (to_integer(value) - 1)) + to_integer((value - 1u32))) == ((to_integer((value -
                    1u32)) + 1) - to_integer(value));
            };
            apply(integer::step_le_lt(to_integer((value - 1u32)), to_integer(value))) using {
                (to_integer((value - 1u32)) + 1) <= to_integer(value);
            };
        }
        normalize() using {
            to_integer((value - 1u32)) < to_integer(value);
        };
    }
}

theorem uint32_increment_upper_bound(value: uint32, upper: uint32) {
    requires value < upper;

    ensures to_integer(value + 1u32) <= to_integer(upper) by {
        have to_integer(value) < to_integer(upper) by {
            known();
        }
        have 0 <= (to_integer(value) + 1) by {
            have 0 <= (to_integer(value) + 1) by {
                have (-1 * to_integer(value)) <= 0 by {
                    have 0 <= to_integer(value) by {
                        normalize();
                    }
                    have (-1 * to_integer(value)) == (0 - to_integer(value)) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer(value), (-1 * to_integer(value)))) using {
                        0 <= to_integer(value);
                        (-1 * to_integer(value)) == (0 - to_integer(value));
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have ((-1 * to_integer(value)) + -1) <= 0 by {
                    have ((-1 * to_integer(value)) + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(integer::add_le((-1 * to_integer(value)), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            (-1 * to_integer(value)) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                        };
                    }
                    have ((-1 * to_integer(value)) + -1) == ((-1 * to_integer(value)) + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute(((-1 * to_integer(value)) + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), ((-1 * to_integer(value)) + -1), 0)) using {
                        ((-1 * to_integer(value)) + (let integer_constant: Integer = -1;
                            integer_constant)) <= (0 + 0);
                        ((-1 * to_integer(value)) + -1) == ((-1 * to_integer(value)) + (let
                            integer_constant: Integer = -1; integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer(value)) + -1) == (0 - (to_integer(value) + 1)) by {
                    normalize();
                }
                apply(integer::difference_le(0, (to_integer(value) + 1), ((-1 * to_integer(value)) + -1))) using {
                    ((-1 * to_integer(value)) + -1) <= 0;
                    ((-1 * to_integer(value)) + -1) == (0 - (to_integer(value) + 1));
                };
            }
            normalize() using {
                0 <= (to_integer(value) + 1);
            };
        }
        have (to_integer(value) + 1) <= 4294967295 by {
            have (to_integer(value) + 1) <= 4294967295 by {
                have (to_integer(value) + (-1 * to_integer(upper)) + 1) <= 0 by {
                    have (to_integer(value) + 1) <= to_integer(upper) by {
                        apply(integer::lt_step_le(to_integer(value), to_integer(upper))) using {
                            to_integer(value) < to_integer(upper);
                        };
                    }
                    have (to_integer(value) + (-1 * to_integer(upper)) + 1) == ((to_integer(value) + 1) - to_integer(upper)) by {
                        normalize();
                    }
                    apply(integer::le_difference((to_integer(value) + 1), to_integer(upper), (to_integer(value) + (-1 * to_integer(upper)) + 1))) using {
                        (to_integer(value) + 1) <= to_integer(upper);
                        (to_integer(value) + (-1 * to_integer(upper)) + 1) == ((to_integer(value) + 1) -
                            to_integer(upper));
                    };
                }
                have (to_integer(upper) + -to_integer(4294967295u64)) <= 0 by {
                    have to_integer(upper) <= 4294967295 by {
                        normalize();
                    }
                    have (to_integer(upper) + -to_integer(4294967295u64)) == (to_integer(upper) - 4294967295) by {
                        normalize();
                    }
                    apply(integer::le_difference(to_integer(upper), 4294967295, (to_integer(upper) + -to_integer(4294967295u64)))) using {
                        to_integer(upper) <= 4294967295;
                        (to_integer(upper) + -to_integer(4294967295u64)) == (to_integer(upper) -
                            4294967295);
                    };
                }
                have (to_integer(value) + -to_integer(4294967294u64)) <= 0 by {
                    have (to_integer(value) + (-1 * to_integer(upper)) + 1 + (to_integer(upper) + -to_integer(4294967295u64))) <= (0 + 0) by {
                        apply(integer::add_le((to_integer(value) + (-1 * to_integer(upper)) + 1), 0, (to_integer(upper) + -to_integer(4294967295u64)), 0)) using {
                            (to_integer(value) + (-1 * to_integer(upper)) + 1) <= 0;
                            (to_integer(upper) + -to_integer(4294967295u64)) <= 0;
                        };
                    }
                    have (to_integer(value) + -to_integer(4294967294u64)) == (to_integer(value) + (-1 * to_integer(upper)) + 1 + (to_integer(upper) + -to_integer(4294967295u64))) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute((to_integer(value) + (-1 * to_integer(upper)) + 1 + (to_integer(upper) + -to_integer(4294967295u64))), (0 + 0), (to_integer(value) + -to_integer(4294967294u64)), 0)) using {
                        (to_integer(value) + (-1 * to_integer(upper)) + 1 + (to_integer(upper) +
                            -to_integer(4294967295u64))) <= (0 + 0);
                        (to_integer(value) + -to_integer(4294967294u64)) == (to_integer(value) + (-1 *
                            to_integer(upper)) + 1 + (to_integer(upper) + -to_integer(4294967295u64)));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer(value) + -to_integer(4294967294u64)) == ((to_integer(value) + 1) - 4294967295) by {
                    normalize();
                }
                apply(integer::difference_le((to_integer(value) + 1), 4294967295, (to_integer(value) + -to_integer(4294967294u64)))) using {
                    (to_integer(value) + -to_integer(4294967294u64)) <= 0;
                    (to_integer(value) + -to_integer(4294967294u64)) == ((to_integer(value) + 1) -
                        4294967295);
                };
            }
            normalize() using {
                (to_integer(value) + 1) <= 4294967295;
            };
        }
        have to_integer((value + 1u32)) == (to_integer(value) + 1) by {
            normalize() using {
                0 <= (to_integer(value) + 1);
                (to_integer(value) + 1) <= 4294967295;
            };
        }
        have to_integer((value + 1u32)) <= to_integer(upper) by {
            have ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32))) == 0 by {
                have (to_integer((value + 1u32)) - (to_integer(value) + 1)) == 0 by {
                    apply(integer::equal_difference(to_integer((value + 1u32)), (to_integer(value) + 1))) using {
                        to_integer((value + 1u32)) == (to_integer(value) + 1);
                    };
                }
                have ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32))) == (to_integer((value + 1u32)) - (to_integer(value) + 1)) by {
                    normalize();
                }
                apply(integer::equal_substitute((to_integer((value + 1u32)) - (to_integer(value) + 1)), 0, ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32))), 0)) using {
                    (to_integer((value + 1u32)) - (to_integer(value) + 1)) == 0;
                    ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32))) == (to_integer((value
                        + 1u32)) - (to_integer(value) + 1));
                    (let integer_value: Integer = 0; integer_value) == 0;
                };
            }
            have ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32))) <= 0 by {
                apply(integer::equal_le(((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32))), 0)) using {
                    ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32))) == 0;
                };
            }
            have (to_integer(value) + (-1 * to_integer(upper)) + 1) <= 0 by {
                have (to_integer(value) + 1) <= to_integer(upper) by {
                    apply(integer::lt_step_le(to_integer(value), to_integer(upper))) using {
                        to_integer(value) < to_integer(upper);
                    };
                }
                have (to_integer(value) + (-1 * to_integer(upper)) + 1) == ((to_integer(value) + 1) - to_integer(upper)) by {
                    normalize();
                }
                apply(integer::le_difference((to_integer(value) + 1), to_integer(upper), (to_integer(value) + (-1 * to_integer(upper)) + 1))) using {
                    (to_integer(value) + 1) <= to_integer(upper);
                    (to_integer(value) + (-1 * to_integer(upper)) + 1) == ((to_integer(value) + 1) -
                        to_integer(upper));
                };
            }
            have (to_integer(value) + (-1 * (to_integer(value) + 1)) + (-1 * to_integer(upper)) + to_integer((value + 1u32)) + 1) <= 0 by {
                have ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32)) + (to_integer(value) + (-1 * to_integer(upper)) + 1)) <= (0 + 0) by {
                    apply(integer::add_le(((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32))), 0, (to_integer(value) + (-1 * to_integer(upper)) + 1), 0)) using {
                        ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32))) <= 0;
                        (to_integer(value) + (-1 * to_integer(upper)) + 1) <= 0;
                    };
                }
                have (to_integer(value) + (-1 * (to_integer(value) + 1)) + (-1 * to_integer(upper)) + to_integer((value + 1u32)) + 1) == ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32)) + (to_integer(value) + (-1 * to_integer(upper)) + 1)) by {
                    normalize();
                }
                have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                    normalize();
                }
                apply(integer::le_substitute(((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32)) + (to_integer(value) + (-1 * to_integer(upper)) + 1)), (0 + 0), (to_integer(value) + (-1 * (to_integer(value) + 1)) + (-1 * to_integer(upper)) + to_integer((value + 1u32)) + 1), 0)) using {
                    ((-1 * (to_integer(value) + 1)) + to_integer((value + 1u32)) + (to_integer(value) +
                        (-1 * to_integer(upper)) + 1)) <= (0 + 0);
                    (to_integer(value) + (-1 * (to_integer(value) + 1)) + (-1 * to_integer(upper)) +
                        to_integer((value + 1u32)) + 1) == ((-1 * (to_integer(value) + 1)) +
                        to_integer((value + 1u32)) + (to_integer(value) + (-1 * to_integer(upper)) +
                        1));
                    (let integer_value: Integer = 0; integer_value) == (0 + 0);
                };
            }
            have (to_integer(value) + (-1 * (to_integer(value) + 1)) + (-1 * to_integer(upper)) + to_integer((value + 1u32)) + 1) == (to_integer((value + 1u32)) - to_integer(upper)) by {
                normalize();
            }
            apply(integer::difference_le(to_integer((value + 1u32)), to_integer(upper), (to_integer(value) + (-1 * (to_integer(value) + 1)) + (-1 * to_integer(upper)) + to_integer((value + 1u32)) + 1))) using {
                (to_integer(value) + (-1 * (to_integer(value) + 1)) + (-1 * to_integer(upper)) +
                    to_integer((value + 1u32)) + 1) <= 0;
                (to_integer(value) + (-1 * (to_integer(value) + 1)) + (-1 * to_integer(upper)) +
                    to_integer((value + 1u32)) + 1) == (to_integer((value + 1u32)) - to_integer(upper));
            };
        }
        normalize() using {
            to_integer((value + 1u32)) <= to_integer(upper);
        };
    }
}

theorem uint32_less_than_implies_positive_difference(value: uint32, upper: uint32) {
    requires value < upper;

    ensures 0 < to_integer(upper - value) by {
        have 0 <= (to_integer(upper) - to_integer(value)) by {
            have 0 <= (to_integer(upper) - to_integer(value)) by {
                have (to_integer(value) + (-1 * to_integer(upper)) + 1) <= 0 by {
                    have (to_integer(value) + 1) <= to_integer(upper) by {
                        apply(integer::lt_step_le(to_integer(value), to_integer(upper))) using {
                            to_integer(value) < to_integer(upper);
                        };
                    }
                    have (to_integer(value) + (-1 * to_integer(upper)) + 1) == ((to_integer(value) + 1) - to_integer(upper)) by {
                        normalize();
                    }
                    apply(integer::le_difference((to_integer(value) + 1), to_integer(upper), (to_integer(value) + (-1 * to_integer(upper)) + 1))) using {
                        (to_integer(value) + 1) <= to_integer(upper);
                        (to_integer(value) + (-1 * to_integer(upper)) + 1) == ((to_integer(value) + 1) -
                            to_integer(upper));
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have (to_integer(value) + (-1 * to_integer(upper))) <= 0 by {
                    have (to_integer(value) + (-1 * to_integer(upper)) + 1 + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(integer::add_le((to_integer(value) + (-1 * to_integer(upper)) + 1), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            (to_integer(value) + (-1 * to_integer(upper)) + 1) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                        };
                    }
                    have (to_integer(value) + (-1 * to_integer(upper))) == (to_integer(value) + (-1 * to_integer(upper)) + 1 + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute((to_integer(value) + (-1 * to_integer(upper)) + 1 + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), (to_integer(value) + (-1 * to_integer(upper))), 0)) using {
                        (to_integer(value) + (-1 * to_integer(upper)) + 1 + (let integer_constant:
                            Integer = -1; integer_constant)) <= (0 + 0);
                        (to_integer(value) + (-1 * to_integer(upper))) == (to_integer(value) + (-1 *
                            to_integer(upper)) + 1 + (let integer_constant: Integer = -1;
                            integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer(value) + (-1 * to_integer(upper))) == (0 - (to_integer(upper) - to_integer(value))) by {
                    normalize();
                }
                apply(integer::difference_le(0, (to_integer(upper) - to_integer(value)), (to_integer(value) + (-1 * to_integer(upper))))) using {
                    (to_integer(value) + (-1 * to_integer(upper))) <= 0;
                    (to_integer(value) + (-1 * to_integer(upper))) == (0 - (to_integer(upper) -
                        to_integer(value)));
                };
            }
            normalize() using {
                0 <= (to_integer(upper) - to_integer(value));
            };
        }
        have (to_integer(upper) - to_integer(value)) <= 4294967295 by {
            have (to_integer(upper) - to_integer(value)) <= 4294967295 by {
                have (to_integer(upper) + -to_integer(4294967295u64)) <= 0 by {
                    have to_integer(upper) <= 4294967295 by {
                        normalize();
                    }
                    have (to_integer(upper) + -to_integer(4294967295u64)) == (to_integer(upper) - 4294967295) by {
                        normalize();
                    }
                    apply(integer::le_difference(to_integer(upper), 4294967295, (to_integer(upper) + -to_integer(4294967295u64)))) using {
                        to_integer(upper) <= 4294967295;
                        (to_integer(upper) + -to_integer(4294967295u64)) == (to_integer(upper) -
                            4294967295);
                    };
                }
                have (-1 * to_integer(value)) <= 0 by {
                    have 0 <= to_integer(value) by {
                        normalize();
                    }
                    have (-1 * to_integer(value)) == (0 - to_integer(value)) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer(value), (-1 * to_integer(value)))) using {
                        0 <= to_integer(value);
                        (-1 * to_integer(value)) == (0 - to_integer(value));
                    };
                }
                have ((-1 * to_integer(value)) + to_integer(upper) + -to_integer(4294967295u64)) <= 0 by {
                    have (to_integer(upper) + -to_integer(4294967295u64) + (-1 * to_integer(value))) <= (0 + 0) by {
                        apply(integer::add_le((to_integer(upper) + -to_integer(4294967295u64)), 0, (-1 * to_integer(value)), 0)) using {
                            (to_integer(upper) + -to_integer(4294967295u64)) <= 0;
                            (-1 * to_integer(value)) <= 0;
                        };
                    }
                    have ((-1 * to_integer(value)) + to_integer(upper) + -to_integer(4294967295u64)) == (to_integer(upper) + -to_integer(4294967295u64) + (-1 * to_integer(value))) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute((to_integer(upper) + -to_integer(4294967295u64) + (-1 * to_integer(value))), (0 + 0), ((-1 * to_integer(value)) + to_integer(upper) + -to_integer(4294967295u64)), 0)) using {
                        (to_integer(upper) + -to_integer(4294967295u64) + (-1 * to_integer(value))) <=
                            (0 + 0);
                        ((-1 * to_integer(value)) + to_integer(upper) + -to_integer(4294967295u64)) ==
                            (to_integer(upper) + -to_integer(4294967295u64) + (-1 * to_integer(value)));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer(value)) + to_integer(upper) + -to_integer(4294967295u64)) == ((to_integer(upper) - to_integer(value)) - 4294967295) by {
                    normalize();
                }
                apply(integer::difference_le((to_integer(upper) - to_integer(value)), 4294967295, ((-1 * to_integer(value)) + to_integer(upper) + -to_integer(4294967295u64)))) using {
                    ((-1 * to_integer(value)) + to_integer(upper) + -to_integer(4294967295u64)) <= 0;
                    ((-1 * to_integer(value)) + to_integer(upper) + -to_integer(4294967295u64)) ==
                        ((to_integer(upper) - to_integer(value)) - 4294967295);
                };
            }
            normalize() using {
                (to_integer(upper) - to_integer(value)) <= 4294967295;
            };
        }
        have to_integer((upper - value)) == (to_integer(upper) - to_integer(value)) by {
            normalize() using {
                0 <= (to_integer(upper) - to_integer(value));
                (to_integer(upper) - to_integer(value)) <= 4294967295;
            };
        }
        have 0 < to_integer((upper - value)) by {
            have ((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value))) == 0 by {
                have (to_integer((upper - value)) - (to_integer(upper) - to_integer(value))) == 0 by {
                    apply(integer::equal_difference(to_integer((upper - value)), (to_integer(upper) - to_integer(value)))) using {
                        to_integer((upper - value)) == (to_integer(upper) - to_integer(value));
                    };
                }
                have ((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value))) == (to_integer((upper - value)) - (to_integer(upper) - to_integer(value))) by {
                    normalize();
                }
                apply(integer::equal_substitute((to_integer((upper - value)) - (to_integer(upper) - to_integer(value))), 0, ((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value))), 0)) using {
                    (to_integer((upper - value)) - (to_integer(upper) - to_integer(value))) == 0;
                    ((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value))) ==
                        (to_integer((upper - value)) - (to_integer(upper) - to_integer(value)));
                    (let integer_value: Integer = 0; integer_value) == 0;
                };
            }
            have ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value)))) <= 0 by {
                have (((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value))) * -1) == (0 * -1) by {
                    apply(integer::equal_multiply(((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value))), 0, -1)) using {
                        ((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value)))
                            == 0;
                    };
                }
                have ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value)))) == 0 by {
                    have ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value)))) == (((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value))) * -1) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 * -1) by {
                        normalize();
                    }
                    apply(integer::equal_substitute((((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value))) * -1), (0 * -1), ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value)))), 0)) using {
                        (((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper - value)))
                            * -1) == (0 * -1);
                        ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))))
                            == (((-1 * (to_integer(upper) - to_integer(value))) + to_integer((upper -
                            value))) * -1);
                        (let integer_value: Integer = 0; integer_value) == (0 * -1);
                    };
                }
                apply(integer::equal_le(((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value)))), 0)) using {
                    ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value)))) == 0;
                };
            }
            have (to_integer(value) + (-1 * to_integer(upper)) + 1) <= 0 by {
                have (to_integer(value) + 1) <= to_integer(upper) by {
                    apply(integer::lt_step_le(to_integer(value), to_integer(upper))) using {
                        to_integer(value) < to_integer(upper);
                    };
                }
                have (to_integer(value) + (-1 * to_integer(upper)) + 1) == ((to_integer(value) + 1) - to_integer(upper)) by {
                    normalize();
                }
                apply(integer::le_difference((to_integer(value) + 1), to_integer(upper), (to_integer(value) + (-1 * to_integer(upper)) + 1))) using {
                    (to_integer(value) + 1) <= to_integer(upper);
                    (to_integer(value) + (-1 * to_integer(upper)) + 1) == ((to_integer(value) + 1) -
                        to_integer(upper));
                };
            }
            have (to_integer(value) + (-1 * to_integer(upper)) + (to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) + 1) <= 0 by {
                have ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) + (to_integer(value) + (-1 * to_integer(upper)) + 1)) <= (0 + 0) by {
                    apply(integer::add_le(((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value)))), 0, (to_integer(value) + (-1 * to_integer(upper)) + 1), 0)) using {
                        ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))))
                            <= 0;
                        (to_integer(value) + (-1 * to_integer(upper)) + 1) <= 0;
                    };
                }
                have (to_integer(value) + (-1 * to_integer(upper)) + (to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) + 1) == ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) + (to_integer(value) + (-1 * to_integer(upper)) + 1)) by {
                    normalize();
                }
                have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                    normalize();
                }
                apply(integer::le_substitute(((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) + (to_integer(value) + (-1 * to_integer(upper)) + 1)), (0 + 0), (to_integer(value) + (-1 * to_integer(upper)) + (to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) + 1), 0)) using {
                    ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) +
                        (to_integer(value) + (-1 * to_integer(upper)) + 1)) <= (0 + 0);
                    (to_integer(value) + (-1 * to_integer(upper)) + (to_integer(upper) -
                        to_integer(value)) + (-1 * to_integer((upper - value))) + 1) ==
                        ((to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) +
                        (to_integer(value) + (-1 * to_integer(upper)) + 1));
                    (let integer_value: Integer = 0; integer_value) == (0 + 0);
                };
            }
            have (to_integer(value) + (-1 * to_integer(upper)) + (to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) + 1) == ((0 + 1) - to_integer((upper - value))) by {
                normalize();
            }
            apply(integer::difference_le((0 + 1), to_integer((upper - value)), (to_integer(value) + (-1 * to_integer(upper)) + (to_integer(upper) - to_integer(value)) + (-1 * to_integer((upper - value))) + 1))) using {
                (to_integer(value) + (-1 * to_integer(upper)) + (to_integer(upper) - to_integer(value))
                    + (-1 * to_integer((upper - value))) + 1) <= 0;
                (to_integer(value) + (-1 * to_integer(upper)) + (to_integer(upper) - to_integer(value))
                    + (-1 * to_integer((upper - value))) + 1) == ((0 + 1) - to_integer((upper -
                    value)));
            };
            apply(integer::step_le_lt(0, to_integer((upper - value)))) using {
                (0 + 1) <= to_integer((upper - value));
            };
        }
        normalize() using {
            0 < to_integer((upper - value));
        };
    }
}

// Neither `bound - value` nor `(bound - 1) - value` wraps under
// `value < bound`, so the measure drops by exactly one.
axiom uint32_difference_decreases_after_increment(value: uint32, bound: uint32) {
    requires value < bound;
    ensures to_integer((0u32 - value) + (bound - 1u32)) < to_integer((0u32 - value) + bound);
}

theorem uint64_less_than_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first < middle;
    requires middle <= last;

    ensures first < last by {
        have to_integer(first) < to_integer(last) by {
            have (to_integer(first) + (-1 * to_integer(middle)) + 1) <= 0 by {
                have to_integer(first) < to_integer(middle) by {
                    normalize() using {
                        first < middle;
                    };
                }
                have (to_integer(first) + 1) <= to_integer(middle) by {
                    apply(integer::lt_step_le(to_integer(first), to_integer(middle))) using {
                        to_integer(first) < to_integer(middle);
                    };
                }
                have (to_integer(first) + (-1 * to_integer(middle)) + 1) == ((to_integer(first) + 1) - to_integer(middle)) by {
                    normalize();
                }
                apply(integer::le_difference((to_integer(first) + 1), to_integer(middle), (to_integer(first) + (-1 * to_integer(middle)) + 1))) using {
                    (to_integer(first) + 1) <= to_integer(middle);
                    (to_integer(first) + (-1 * to_integer(middle)) + 1) == ((to_integer(first) + 1) -
                        to_integer(middle));
                };
            }
            have ((-1 * to_integer(last)) + to_integer(middle)) <= 0 by {
                have to_integer(middle) <= to_integer(last) by {
                    normalize() using {
                        middle <= last;
                    };
                }
                have ((-1 * to_integer(last)) + to_integer(middle)) == (to_integer(middle) - to_integer(last)) by {
                    normalize();
                }
                apply(integer::le_difference(to_integer(middle), to_integer(last), ((-1 * to_integer(last)) + to_integer(middle)))) using {
                    to_integer(middle) <= to_integer(last);
                    ((-1 * to_integer(last)) + to_integer(middle)) == (to_integer(middle) -
                        to_integer(last));
                };
            }
            have (to_integer(first) + (-1 * to_integer(last)) + 1) <= 0 by {
                have (to_integer(first) + (-1 * to_integer(middle)) + 1 + ((-1 * to_integer(last)) + to_integer(middle))) <= (0 + 0) by {
                    apply(integer::add_le((to_integer(first) + (-1 * to_integer(middle)) + 1), 0, ((-1 * to_integer(last)) + to_integer(middle)), 0)) using {
                        (to_integer(first) + (-1 * to_integer(middle)) + 1) <= 0;
                        ((-1 * to_integer(last)) + to_integer(middle)) <= 0;
                    };
                }
                have (to_integer(first) + (-1 * to_integer(last)) + 1) == (to_integer(first) + (-1 * to_integer(middle)) + 1 + ((-1 * to_integer(last)) + to_integer(middle))) by {
                    normalize();
                }
                have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                    normalize();
                }
                apply(integer::le_substitute((to_integer(first) + (-1 * to_integer(middle)) + 1 + ((-1 * to_integer(last)) + to_integer(middle))), (0 + 0), (to_integer(first) + (-1 * to_integer(last)) + 1), 0)) using {
                    (to_integer(first) + (-1 * to_integer(middle)) + 1 + ((-1 * to_integer(last)) +
                        to_integer(middle))) <= (0 + 0);
                    (to_integer(first) + (-1 * to_integer(last)) + 1) == (to_integer(first) + (-1 *
                        to_integer(middle)) + 1 + ((-1 * to_integer(last)) + to_integer(middle)));
                    (let integer_value: Integer = 0; integer_value) == (0 + 0);
                };
            }
            have (to_integer(first) + (-1 * to_integer(last)) + 1) == ((to_integer(first) + 1) - to_integer(last)) by {
                normalize();
            }
            apply(integer::difference_le((to_integer(first) + 1), to_integer(last), (to_integer(first) + (-1 * to_integer(last)) + 1))) using {
                (to_integer(first) + (-1 * to_integer(last)) + 1) <= 0;
                (to_integer(first) + (-1 * to_integer(last)) + 1) == ((to_integer(first) + 1) -
                    to_integer(last));
            };
            apply(integer::step_le_lt(to_integer(first), to_integer(last))) using {
                (to_integer(first) + 1) <= to_integer(last);
            };
        }
        normalize() using {
            to_integer(first) < to_integer(last);
        };
    }
}

theorem uint64_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        have to_integer(first) <= to_integer(last) by {
            have (to_integer(first) + (-1 * to_integer(middle))) <= 0 by {
                have to_integer(first) <= to_integer(middle) by {
                    normalize() using {
                        first <= middle;
                    };
                }
                have (to_integer(first) + (-1 * to_integer(middle))) == (to_integer(first) - to_integer(middle)) by {
                    normalize();
                }
                apply(integer::le_difference(to_integer(first), to_integer(middle), (to_integer(first) + (-1 * to_integer(middle))))) using {
                    to_integer(first) <= to_integer(middle);
                    (to_integer(first) + (-1 * to_integer(middle))) == (to_integer(first) -
                        to_integer(middle));
                };
            }
            have ((-1 * to_integer(last)) + to_integer(middle)) <= 0 by {
                have to_integer(middle) <= to_integer(last) by {
                    normalize() using {
                        middle <= last;
                    };
                }
                have ((-1 * to_integer(last)) + to_integer(middle)) == (to_integer(middle) - to_integer(last)) by {
                    normalize();
                }
                apply(integer::le_difference(to_integer(middle), to_integer(last), ((-1 * to_integer(last)) + to_integer(middle)))) using {
                    to_integer(middle) <= to_integer(last);
                    ((-1 * to_integer(last)) + to_integer(middle)) == (to_integer(middle) -
                        to_integer(last));
                };
            }
            have (to_integer(first) + (-1 * to_integer(last))) <= 0 by {
                have (to_integer(first) + (-1 * to_integer(middle)) + ((-1 * to_integer(last)) + to_integer(middle))) <= (0 + 0) by {
                    apply(integer::add_le((to_integer(first) + (-1 * to_integer(middle))), 0, ((-1 * to_integer(last)) + to_integer(middle)), 0)) using {
                        (to_integer(first) + (-1 * to_integer(middle))) <= 0;
                        ((-1 * to_integer(last)) + to_integer(middle)) <= 0;
                    };
                }
                have (to_integer(first) + (-1 * to_integer(last))) == (to_integer(first) + (-1 * to_integer(middle)) + ((-1 * to_integer(last)) + to_integer(middle))) by {
                    normalize();
                }
                have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                    normalize();
                }
                apply(integer::le_substitute((to_integer(first) + (-1 * to_integer(middle)) + ((-1 * to_integer(last)) + to_integer(middle))), (0 + 0), (to_integer(first) + (-1 * to_integer(last))), 0)) using {
                    (to_integer(first) + (-1 * to_integer(middle)) + ((-1 * to_integer(last)) +
                        to_integer(middle))) <= (0 + 0);
                    (to_integer(first) + (-1 * to_integer(last))) == (to_integer(first) + (-1 *
                        to_integer(middle)) + ((-1 * to_integer(last)) + to_integer(middle)));
                    (let integer_value: Integer = 0; integer_value) == (0 + 0);
                };
            }
            have (to_integer(first) + (-1 * to_integer(last))) == (to_integer(first) - to_integer(last)) by {
                normalize();
            }
            apply(integer::difference_le(to_integer(first), to_integer(last), (to_integer(first) + (-1 * to_integer(last))))) using {
                (to_integer(first) + (-1 * to_integer(last))) <= 0;
                (to_integer(first) + (-1 * to_integer(last))) == (to_integer(first) - to_integer(last));
            };
        }
        normalize() using {
            to_integer(first) <= to_integer(last);
        };
    }
}

theorem int32_nonnegative_predecessor_upper_bound(value: int32, bound: int32) {
    requires 0 <= value;
    requires value <= bound;

    ensures to_integer(value - 1) <= to_integer(bound) by {
        have 0 <= to_integer((value as int32)) by {
            normalize() using {
                ((0 as int32) as int32) <= ((value as int32) as int32);
            };
        }
        have to_integer((value as int32)) <= 2147483647 by {
            normalize() using {
                ((0 as int32) as int32) <= ((value as int32) as int32);
            };
        }
        have 1 <= to_integer((1 as int32)) by {
            normalize() using {};
        }
        have to_integer((1 as int32)) <= 1 by {
            normalize() using {};
        }
        have -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32))) by {
            have -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32))) by {
                have (-1 * to_integer((value as int32))) <= 0 by {
                    have (-1 * to_integer((value as int32))) == (0 - to_integer((value as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(0, to_integer((value as int32)), (-1 * to_integer((value as int32))))) using {
                        0 <= to_integer((value as int32));
                        (-1 * to_integer((value as int32))) == (0 - to_integer((value as int32)));
                    };
                }
                have (let integer_constant: Integer = -2147483647; integer_constant) <= 0 by {
                    normalize();
                }
                have ((-1 * to_integer((value as int32))) + -2147483647) <= 0 by {
                    have ((-1 * to_integer((value as int32))) + (let integer_constant: Integer = -2147483647; integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le((-1 * to_integer((value as int32))), 0, (let integer_constant: Integer = -2147483647; integer_constant), 0)) using {
                            (-1 * to_integer((value as int32))) <= 0;
                            (let integer_constant: Integer = -2147483647; integer_constant) <= 0;
                        };
                    }
                    have ((-1 * to_integer((value as int32))) + -2147483647) == ((-1 * to_integer((value as int32))) + (let integer_constant: Integer = -2147483647; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute(((-1 * to_integer((value as int32))) + (let integer_constant: Integer = -2147483647; integer_constant)), (0 + 0), ((-1 * to_integer((value as int32))) + -2147483647), 0)) using {
                        ((-1 * to_integer((value as int32))) + (let integer_constant: Integer =
                            -2147483647; integer_constant)) <= (0 + 0);
                        ((-1 * to_integer((value as int32))) + -2147483647) == ((-1 * to_integer((value
                            as int32))) + (let integer_constant: Integer = -2147483647;
                            integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer((value as int32))) + -2147483647) == (-2147483648 - (to_integer((value as int32)) - to_integer((1 as int32)))) by {
                    normalize();
                }
                apply(click::integer::difference_le(-2147483648, (to_integer((value as int32)) - to_integer((1 as int32))), ((-1 * to_integer((value as int32))) + -2147483647))) using {
                    ((-1 * to_integer((value as int32))) + -2147483647) <= 0;
                    ((-1 * to_integer((value as int32))) + -2147483647) == (-2147483648 -
                        (to_integer((value as int32)) - to_integer((1 as int32))));
                };
            }
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32)));
            };
        }
        have (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647 by {
            have (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647 by {
                have (to_integer((value as int32)) + -2147483647) <= 0 by {
                    have (to_integer((value as int32)) + -2147483647) == (to_integer((value as int32)) - 2147483647) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((value as int32)), 2147483647, (to_integer((value as int32)) + -2147483647))) using {
                        to_integer((value as int32)) <= 2147483647;
                        (to_integer((value as int32)) + -2147483647) == (to_integer((value as int32)) -
                            2147483647);
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have (to_integer((value as int32)) + -to_integer(2147483648u64)) <= 0 by {
                    have (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer((value as int32)) + -2147483647), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            (to_integer((value as int32)) + -2147483647) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                        };
                    }
                    have (to_integer((value as int32)) + -to_integer(2147483648u64)) == (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), (to_integer((value as int32)) + -to_integer(2147483648u64)), 0)) using {
                        (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer =
                            -1; integer_constant)) <= (0 + 0);
                        (to_integer((value as int32)) + -to_integer(2147483648u64)) ==
                            (to_integer((value as int32)) + -2147483647 + (let integer_constant: Integer
                            = -1; integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer((value as int32)) + -to_integer(2147483648u64)) == ((to_integer((value as int32)) - to_integer((1 as int32))) - 2147483647) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer((value as int32)) - to_integer((1 as int32))), 2147483647, (to_integer((value as int32)) + -to_integer(2147483648u64)))) using {
                    (to_integer((value as int32)) + -to_integer(2147483648u64)) <= 0;
                    (to_integer((value as int32)) + -to_integer(2147483648u64)) == ((to_integer((value
                        as int32)) - to_integer((1 as int32))) - 2147483647);
                };
            }
            normalize() using {
                (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647;
            };
        }
        have defined((value - 1)) by {
            known();
        }
        have to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as int32))) by {
            normalize() using {
                -2147483648 <= (to_integer((value as int32)) - to_integer((1 as int32)));
                (to_integer((value as int32)) - to_integer((1 as int32))) <= 2147483647;
            };
        }
        have -1 <= to_integer(((value - 1) as int32)) by {
            normalize() using {
                0 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                0 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        have to_integer(((value - 1) as int32)) <= 2147483646 by {
            normalize() using {
                0 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                1 <= to_integer((1 as int32));
                to_integer((1 as int32)) <= 1;
                0 <= to_integer((value as int32));
                to_integer((value as int32)) <= 2147483647;
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        have -1 <= 0 by {
            normalize() using {
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        have (to_integer(((value as int32) as int32)) + -1) <= (to_integer(((bound as int32) as int32)) + 0) by {
            have defined(((value - 1) as int32)) by {
                known();
            }
            have defined((value - 1)) by {
                known();
            }
            have defined(old(((value - 1) as int32))) by {
                known();
            }
            have defined(old((value - 1))) by {
                known();
            }
            have (to_integer(((value as int32) as int32)) + -1) <= (to_integer(((bound as int32) as int32)) + 0) by {
                have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32)))) <= 0 by {
                    have to_integer((((value as int32) as int32) as int32)) <= to_integer((((bound as int32) as int32) as int32)) by {
                        normalize() using {
                            ((value as int32) as int32) <= ((bound as int32) as int32);
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32)))) == (to_integer((((value as int32) as int32) as int32)) - to_integer((((bound as int32) as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((((value as int32) as int32) as int32)), to_integer((((bound as int32) as int32) as int32)), (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32)))))) using {
                        to_integer((((value as int32) as int32) as int32)) <= to_integer((((bound as
                            int32) as int32) as int32));
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound
                            as int32) as int32) as int32)))) == (to_integer((((value as int32) as int32)
                            as int32)) - to_integer((((bound as int32) as int32) as int32)));
                        defined(((value - 1) as int32));
                        defined((value - 1));
                        defined(old(((value - 1) as int32)));
                        defined(old((value - 1)));
                    };
                }
                have (let integer_constant: Integer = -1; integer_constant) <= 0 by {
                    normalize();
                }
                have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32))) + -1) <= 0 by {
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32))) + (let integer_constant: Integer = -1; integer_constant)) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32)))), 0, (let integer_constant: Integer = -1; integer_constant), 0)) using {
                            (to_integer((((value as int32) as int32) as int32)) + (-1 *
                                to_integer((((bound as int32) as int32) as int32)))) <= 0;
                            (let integer_constant: Integer = -1; integer_constant) <= 0;
                            defined(((value - 1) as int32));
                            defined((value - 1));
                            defined(old(((value - 1) as int32)));
                            defined(old((value - 1)));
                        };
                    }
                    have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32))) + -1) == (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32))) + (let integer_constant: Integer = -1; integer_constant)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32))) + (let integer_constant: Integer = -1; integer_constant)), (0 + 0), (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32))) + -1), 0)) using {
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound
                            as int32) as int32) as int32))) + (let integer_constant: Integer = -1;
                            integer_constant)) <= (0 + 0);
                        (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound
                            as int32) as int32) as int32))) + -1) == (to_integer((((value as int32) as
                            int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as
                            int32))) + (let integer_constant: Integer = -1; integer_constant));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                        defined(((value - 1) as int32));
                        defined((value - 1));
                        defined(old(((value - 1) as int32)));
                        defined(old((value - 1)));
                    };
                }
                have (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32))) + -1) == ((to_integer(((value as int32) as int32)) + -1) - (to_integer(((bound as int32) as int32)) + 0)) by {
                    normalize();
                }
                apply(click::integer::difference_le((to_integer(((value as int32) as int32)) + -1), (to_integer(((bound as int32) as int32)) + 0), (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as int32) as int32) as int32))) + -1))) using {
                    (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as
                        int32) as int32) as int32))) + -1) <= 0;
                    (to_integer((((value as int32) as int32) as int32)) + (-1 * to_integer((((bound as
                        int32) as int32) as int32))) + -1) == ((to_integer(((value as int32) as int32))
                        + -1) - (to_integer(((bound as int32) as int32)) + 0));
                    defined(((value - 1) as int32));
                    defined((value - 1));
                    defined(old(((value - 1) as int32)));
                    defined(old((value - 1)));
                };
            }
            normalize() using {
                (to_integer(((value as int32) as int32)) + -1) <= (to_integer(((bound as int32) as
                    int32)) + 0);
            };
        }
        have ((value - 1) as int32) <= (bound as int32) by {
            have defined(((value - 1) as int32)) by {
                known();
            }
            have defined((value - 1)) by {
                known();
            }
            have defined(old(((value - 1) as int32))) by {
                known();
            }
            have defined(old((value - 1))) by {
                known();
            }
            have to_integer((((value - 1) as int32) as int32)) <= to_integer(((bound as int32) as int32)) by {
                have (to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as int32) as int32)) + 0))) <= 0 by {
                    have (to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as int32) as int32)) + 0))) == ((to_integer(((value as int32) as int32)) + -1) - (to_integer(((bound as int32) as int32)) + 0)) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer(((value as int32) as int32)) + -1), (to_integer(((bound as int32) as int32)) + 0), (to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as int32) as int32)) + 0))))) using {
                        (to_integer(((value as int32) as int32)) + -1) <= (to_integer(((bound as int32)
                            as int32)) + 0);
                        (to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as
                            int32) as int32)) + 0))) == ((to_integer(((value as int32) as int32)) + -1)
                            - (to_integer(((bound as int32) as int32)) + 0));
                        defined(((value - 1) as int32));
                        defined((value - 1));
                        defined(old(((value - 1) as int32)));
                        defined(old((value - 1)));
                    };
                }
                have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))) == 0 by {
                    have (to_integer(((value - 1) as int32)) - (to_integer((value as int32)) - to_integer((1 as int32)))) == 0 by {
                        apply(click::integer::equal_difference(to_integer(((value - 1) as int32)), (to_integer((value as int32)) - to_integer((1 as int32))))) using {
                            to_integer(((value - 1) as int32)) == (to_integer((value as int32)) -
                                to_integer((1 as int32)));
                            defined(((value - 1) as int32));
                            defined((value - 1));
                            defined(old(((value - 1) as int32)));
                            defined(old((value - 1)));
                        };
                    }
                    have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))) == (to_integer(((value - 1) as int32)) - (to_integer((value as int32)) - to_integer((1 as int32)))) by {
                        normalize();
                    }
                    apply(click::integer::equal_substitute((to_integer(((value - 1) as int32)) - (to_integer((value as int32)) - to_integer((1 as int32)))), 0, ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))), 0)) using {
                        (to_integer(((value - 1) as int32)) - (to_integer((value as int32)) -
                            to_integer((1 as int32)))) == 0;
                        ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                            to_integer(((value - 1) as int32))) == (to_integer(((value - 1) as int32)) -
                            (to_integer((value as int32)) - to_integer((1 as int32))));
                        (let integer_value: Integer = 0; integer_value) == 0;
                        defined(((value - 1) as int32));
                        defined((value - 1));
                        defined(old(((value - 1) as int32)));
                        defined(old((value - 1)));
                    };
                }
                have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))) <= 0 by {
                    apply(click::integer::equal_le(((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))), 0)) using {
                        ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                            to_integer(((value - 1) as int32))) == 0;
                        defined(((value - 1) as int32));
                        defined((value - 1));
                        defined(old(((value - 1) as int32)));
                        defined(old((value - 1)));
                    };
                }
                have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32)) + (to_integer(((value as int32) as int32)) + -1) + (-1 * (to_integer(((bound as int32) as int32)) + 0))) <= 0 by {
                    have (to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as int32) as int32)) + 0)) + ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32)))) <= (0 + 0) by {
                        apply(click::integer::add_le((to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as int32) as int32)) + 0))), 0, ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32))), 0)) using {
                            (to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as
                                int32) as int32)) + 0))) <= 0;
                            ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                                to_integer(((value - 1) as int32))) <= 0;
                            defined(((value - 1) as int32));
                            defined((value - 1));
                            defined(old(((value - 1) as int32)));
                            defined(old((value - 1)));
                        };
                    }
                    have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32)) + (to_integer(((value as int32) as int32)) + -1) + (-1 * (to_integer(((bound as int32) as int32)) + 0))) == (to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as int32) as int32)) + 0)) + ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32)))) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute((to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as int32) as int32)) + 0)) + ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32)))), (0 + 0), ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32)) + (to_integer(((value as int32) as int32)) + -1) + (-1 * (to_integer(((bound as int32) as int32)) + 0))), 0)) using {
                        (to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as
                            int32) as int32)) + 0)) + ((-1 * (to_integer((value as int32)) -
                            to_integer((1 as int32)))) + to_integer(((value - 1) as int32)))) <= (0 +
                            0);
                        ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                            to_integer(((value - 1) as int32)) + (to_integer(((value as int32) as
                            int32)) + -1) + (-1 * (to_integer(((bound as int32) as int32)) + 0))) ==
                            (to_integer(((value as int32) as int32)) + -1 + (-1 * (to_integer(((bound as
                            int32) as int32)) + 0)) + ((-1 * (to_integer((value as int32)) -
                            to_integer((1 as int32)))) + to_integer(((value - 1) as int32))));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                        defined(((value - 1) as int32));
                        defined((value - 1));
                        defined(old(((value - 1) as int32)));
                        defined(old((value - 1)));
                    };
                }
                have ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32)) + (to_integer(((value as int32) as int32)) + -1) + (-1 * (to_integer(((bound as int32) as int32)) + 0))) == (to_integer((((value - 1) as int32) as int32)) - to_integer(((bound as int32) as int32))) by {
                    normalize();
                }
                apply(click::integer::difference_le(to_integer((((value - 1) as int32) as int32)), to_integer(((bound as int32) as int32)), ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) + to_integer(((value - 1) as int32)) + (to_integer(((value as int32) as int32)) + -1) + (-1 * (to_integer(((bound as int32) as int32)) + 0))))) using {
                    ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                        to_integer(((value - 1) as int32)) + (to_integer(((value as int32) as int32)) +
                        -1) + (-1 * (to_integer(((bound as int32) as int32)) + 0))) <= 0;
                    ((-1 * (to_integer((value as int32)) - to_integer((1 as int32)))) +
                        to_integer(((value - 1) as int32)) + (to_integer(((value as int32) as int32)) +
                        -1) + (-1 * (to_integer(((bound as int32) as int32)) + 0))) ==
                        (to_integer((((value - 1) as int32) as int32)) - to_integer(((bound as int32) as
                        int32)));
                    defined(((value - 1) as int32));
                    defined((value - 1));
                    defined(old(((value - 1) as int32)));
                    defined(old((value - 1)));
                };
            }
            normalize() using {
                to_integer((((value - 1) as int32) as int32)) <= to_integer(((bound as int32) as
                    int32));
            };
        }
        have to_integer((value - 1)) <= to_integer(bound) by {
            normalize() using {
                ((value - 1) as int32) <= (bound as int32);
                to_integer(((value - 1) as int32)) == (to_integer((value as int32)) - to_integer((1 as
                    int32)));
            };
        }
        known();
    }
}

theorem int32_less_equal_less_than_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last by {
        have to_integer((first as int32)) < to_integer((last as int32)) by {
            have ((-1 * to_integer((middle as int32))) + to_integer((first as int32))) <= 0 by {
                have to_integer((first as int32)) <= to_integer((middle as int32)) by {
                    normalize() using {
                        first <= middle;
                    };
                }
                have ((-1 * to_integer((middle as int32))) + to_integer((first as int32))) == (to_integer((first as int32)) - to_integer((middle as int32))) by {
                    normalize();
                }
                apply(integer::le_difference(to_integer((first as int32)), to_integer((middle as int32)), ((-1 * to_integer((middle as int32))) + to_integer((first as int32))))) using {
                    to_integer((first as int32)) <= to_integer((middle as int32));
                    ((-1 * to_integer((middle as int32))) + to_integer((first as int32))) ==
                        (to_integer((first as int32)) - to_integer((middle as int32)));
                };
            }
            have (to_integer((middle as int32)) + (-1 * to_integer((last as int32))) + 1) <= 0 by {
                have to_integer((middle as int32)) < to_integer((last as int32)) by {
                    normalize() using {
                        middle < last;
                    };
                }
                have (to_integer((middle as int32)) + 1) <= to_integer((last as int32)) by {
                    apply(integer::lt_step_le(to_integer((middle as int32)), to_integer((last as int32)))) using {
                        to_integer((middle as int32)) < to_integer((last as int32));
                    };
                }
                have (to_integer((middle as int32)) + (-1 * to_integer((last as int32))) + 1) == ((to_integer((middle as int32)) + 1) - to_integer((last as int32))) by {
                    normalize();
                }
                apply(integer::le_difference((to_integer((middle as int32)) + 1), to_integer((last as int32)), (to_integer((middle as int32)) + (-1 * to_integer((last as int32))) + 1))) using {
                    (to_integer((middle as int32)) + 1) <= to_integer((last as int32));
                    (to_integer((middle as int32)) + (-1 * to_integer((last as int32))) + 1) ==
                        ((to_integer((middle as int32)) + 1) - to_integer((last as int32)));
                };
            }
            have (to_integer((first as int32)) + (-1 * to_integer((last as int32))) + 1) <= 0 by {
                have ((-1 * to_integer((middle as int32))) + to_integer((first as int32)) + (to_integer((middle as int32)) + (-1 * to_integer((last as int32))) + 1)) <= (0 + 0) by {
                    apply(integer::add_le(((-1 * to_integer((middle as int32))) + to_integer((first as int32))), 0, (to_integer((middle as int32)) + (-1 * to_integer((last as int32))) + 1), 0)) using {
                        ((-1 * to_integer((middle as int32))) + to_integer((first as int32))) <= 0;
                        (to_integer((middle as int32)) + (-1 * to_integer((last as int32))) + 1) <= 0;
                    };
                }
                have (to_integer((first as int32)) + (-1 * to_integer((last as int32))) + 1) == ((-1 * to_integer((middle as int32))) + to_integer((first as int32)) + (to_integer((middle as int32)) + (-1 * to_integer((last as int32))) + 1)) by {
                    normalize();
                }
                have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                    normalize();
                }
                apply(integer::le_substitute(((-1 * to_integer((middle as int32))) + to_integer((first as int32)) + (to_integer((middle as int32)) + (-1 * to_integer((last as int32))) + 1)), (0 + 0), (to_integer((first as int32)) + (-1 * to_integer((last as int32))) + 1), 0)) using {
                    ((-1 * to_integer((middle as int32))) + to_integer((first as int32)) +
                        (to_integer((middle as int32)) + (-1 * to_integer((last as int32))) + 1)) <= (0
                        + 0);
                    (to_integer((first as int32)) + (-1 * to_integer((last as int32))) + 1) == ((-1 *
                        to_integer((middle as int32))) + to_integer((first as int32)) +
                        (to_integer((middle as int32)) + (-1 * to_integer((last as int32))) + 1));
                    (let integer_value: Integer = 0; integer_value) == (0 + 0);
                };
            }
            have (to_integer((first as int32)) + (-1 * to_integer((last as int32))) + 1) == ((to_integer((first as int32)) + 1) - to_integer((last as int32))) by {
                normalize();
            }
            apply(integer::difference_le((to_integer((first as int32)) + 1), to_integer((last as int32)), (to_integer((first as int32)) + (-1 * to_integer((last as int32))) + 1))) using {
                (to_integer((first as int32)) + (-1 * to_integer((last as int32))) + 1) <= 0;
                (to_integer((first as int32)) + (-1 * to_integer((last as int32))) + 1) ==
                    ((to_integer((first as int32)) + 1) - to_integer((last as int32)));
            };
            apply(integer::step_le_lt(to_integer((first as int32)), to_integer((last as int32)))) using {
                (to_integer((first as int32)) + 1) <= to_integer((last as int32));
            };
        }
        normalize() using {
            to_integer((first as int32)) < to_integer((last as int32));
        };
    }
}

theorem int32_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        have to_integer((first as int32)) <= to_integer((last as int32)) by {
            have ((-1 * to_integer((middle as int32))) + to_integer((first as int32))) <= 0 by {
                have to_integer((first as int32)) <= to_integer((middle as int32)) by {
                    normalize() using {
                        first <= middle;
                    };
                }
                have ((-1 * to_integer((middle as int32))) + to_integer((first as int32))) == (to_integer((first as int32)) - to_integer((middle as int32))) by {
                    normalize();
                }
                apply(integer::le_difference(to_integer((first as int32)), to_integer((middle as int32)), ((-1 * to_integer((middle as int32))) + to_integer((first as int32))))) using {
                    to_integer((first as int32)) <= to_integer((middle as int32));
                    ((-1 * to_integer((middle as int32))) + to_integer((first as int32))) ==
                        (to_integer((first as int32)) - to_integer((middle as int32)));
                };
            }
            have (to_integer((middle as int32)) + (-1 * to_integer((last as int32)))) <= 0 by {
                have to_integer((middle as int32)) <= to_integer((last as int32)) by {
                    normalize() using {
                        middle <= last;
                    };
                }
                have (to_integer((middle as int32)) + (-1 * to_integer((last as int32)))) == (to_integer((middle as int32)) - to_integer((last as int32))) by {
                    normalize();
                }
                apply(integer::le_difference(to_integer((middle as int32)), to_integer((last as int32)), (to_integer((middle as int32)) + (-1 * to_integer((last as int32)))))) using {
                    to_integer((middle as int32)) <= to_integer((last as int32));
                    (to_integer((middle as int32)) + (-1 * to_integer((last as int32)))) ==
                        (to_integer((middle as int32)) - to_integer((last as int32)));
                };
            }
            have (to_integer((first as int32)) + (-1 * to_integer((last as int32)))) <= 0 by {
                have ((-1 * to_integer((middle as int32))) + to_integer((first as int32)) + (to_integer((middle as int32)) + (-1 * to_integer((last as int32))))) <= (0 + 0) by {
                    apply(integer::add_le(((-1 * to_integer((middle as int32))) + to_integer((first as int32))), 0, (to_integer((middle as int32)) + (-1 * to_integer((last as int32)))), 0)) using {
                        ((-1 * to_integer((middle as int32))) + to_integer((first as int32))) <= 0;
                        (to_integer((middle as int32)) + (-1 * to_integer((last as int32)))) <= 0;
                    };
                }
                have (to_integer((first as int32)) + (-1 * to_integer((last as int32)))) == ((-1 * to_integer((middle as int32))) + to_integer((first as int32)) + (to_integer((middle as int32)) + (-1 * to_integer((last as int32))))) by {
                    normalize();
                }
                have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                    normalize();
                }
                apply(integer::le_substitute(((-1 * to_integer((middle as int32))) + to_integer((first as int32)) + (to_integer((middle as int32)) + (-1 * to_integer((last as int32))))), (0 + 0), (to_integer((first as int32)) + (-1 * to_integer((last as int32)))), 0)) using {
                    ((-1 * to_integer((middle as int32))) + to_integer((first as int32)) +
                        (to_integer((middle as int32)) + (-1 * to_integer((last as int32))))) <= (0 +
                        0);
                    (to_integer((first as int32)) + (-1 * to_integer((last as int32)))) == ((-1 *
                        to_integer((middle as int32))) + to_integer((first as int32)) +
                        (to_integer((middle as int32)) + (-1 * to_integer((last as int32)))));
                    (let integer_value: Integer = 0; integer_value) == (0 + 0);
                };
            }
            have (to_integer((first as int32)) + (-1 * to_integer((last as int32)))) == (to_integer((first as int32)) - to_integer((last as int32))) by {
                normalize();
            }
            apply(integer::difference_le(to_integer((first as int32)), to_integer((last as int32)), (to_integer((first as int32)) + (-1 * to_integer((last as int32)))))) using {
                (to_integer((first as int32)) + (-1 * to_integer((last as int32)))) <= 0;
                (to_integer((first as int32)) + (-1 * to_integer((last as int32)))) ==
                    (to_integer((first as int32)) - to_integer((last as int32)));
            };
        }
        normalize() using {
            to_integer((first as int32)) <= to_integer((last as int32));
        };
    }
}

theorem int32_less_equal_and_not_less_than_implies_equal(left: int32, right: int32) {
    requires left <= right;
    requires not (left < right);

    ensures left == right by {
        have to_integer((left as int32)) == to_integer((right as int32)) by {
            have ((-1 * to_integer((right as int32))) + to_integer((left as int32))) <= 0 by {
                have to_integer((left as int32)) <= to_integer((right as int32)) by {
                    normalize() using {
                        left <= right;
                    };
                }
                have ((-1 * to_integer((right as int32))) + to_integer((left as int32))) == (to_integer((left as int32)) - to_integer((right as int32))) by {
                    normalize();
                }
                apply(integer::le_difference(to_integer((left as int32)), to_integer((right as int32)), ((-1 * to_integer((right as int32))) + to_integer((left as int32))))) using {
                    to_integer((left as int32)) <= to_integer((right as int32));
                    ((-1 * to_integer((right as int32))) + to_integer((left as int32))) ==
                        (to_integer((left as int32)) - to_integer((right as int32)));
                };
            }
            have (to_integer((right as int32)) + (-1 * to_integer((left as int32)))) <= 0 by {
                have to_integer((right as int32)) <= to_integer((left as int32)) by {
                    normalize() using {
                        not left < right;
                    };
                }
                have (to_integer((right as int32)) + (-1 * to_integer((left as int32)))) == (to_integer((right as int32)) - to_integer((left as int32))) by {
                    normalize();
                }
                apply(integer::le_difference(to_integer((right as int32)), to_integer((left as int32)), (to_integer((right as int32)) + (-1 * to_integer((left as int32)))))) using {
                    to_integer((right as int32)) <= to_integer((left as int32));
                    (to_integer((right as int32)) + (-1 * to_integer((left as int32)))) ==
                        (to_integer((right as int32)) - to_integer((left as int32)));
                };
            }
            have ((-1 * to_integer((right as int32))) + to_integer((left as int32))) == 0 by {
                have ((-1 * to_integer((right as int32))) + to_integer((left as int32))) <= ((-1 * to_integer((right as int32))) + to_integer((left as int32))) by {
                    normalize();
                }
                have (to_integer((right as int32)) + (-1 * to_integer((left as int32))) + ((-1 * to_integer((right as int32))) + to_integer((left as int32)))) <= (0 + ((-1 * to_integer((right as int32))) + to_integer((left as int32)))) by {
                    apply(integer::add_le((to_integer((right as int32)) + (-1 * to_integer((left as int32)))), 0, ((-1 * to_integer((right as int32))) + to_integer((left as int32))), ((-1 * to_integer((right as int32))) + to_integer((left as int32))))) using {
                        (to_integer((right as int32)) + (-1 * to_integer((left as int32)))) <= 0;
                        ((-1 * to_integer((right as int32))) + to_integer((left as int32))) <= ((-1 *
                            to_integer((right as int32))) + to_integer((left as int32)));
                    };
                }
                have 0 <= ((-1 * to_integer((right as int32))) + to_integer((left as int32))) by {
                    have 0 == (to_integer((right as int32)) + (-1 * to_integer((left as int32))) + ((-1 * to_integer((right as int32))) + to_integer((left as int32)))) by {
                        normalize();
                    }
                    have ((-1 * to_integer((right as int32))) + to_integer((left as int32))) == (0 + ((-1 * to_integer((right as int32))) + to_integer((left as int32)))) by {
                        normalize();
                    }
                    apply(integer::le_substitute((to_integer((right as int32)) + (-1 * to_integer((left as int32))) + ((-1 * to_integer((right as int32))) + to_integer((left as int32)))), (0 + ((-1 * to_integer((right as int32))) + to_integer((left as int32)))), 0, ((-1 * to_integer((right as int32))) + to_integer((left as int32))))) using {
                        (to_integer((right as int32)) + (-1 * to_integer((left as int32))) + ((-1 *
                            to_integer((right as int32))) + to_integer((left as int32)))) <= (0 + ((-1 *
                            to_integer((right as int32))) + to_integer((left as int32))));
                        0 == (to_integer((right as int32)) + (-1 * to_integer((left as int32))) + ((-1 *
                            to_integer((right as int32))) + to_integer((left as int32))));
                        ((-1 * to_integer((right as int32))) + to_integer((left as int32))) == (0 + ((-1
                            * to_integer((right as int32))) + to_integer((left as int32))));
                    };
                }
                apply(integer::le_antisymmetric(((-1 * to_integer((right as int32))) + to_integer((left as int32))), 0)) using {
                    ((-1 * to_integer((right as int32))) + to_integer((left as int32))) <= 0;
                    0 <= ((-1 * to_integer((right as int32))) + to_integer((left as int32)));
                };
            }
            have ((-1 * to_integer((right as int32))) + to_integer((left as int32)) + to_integer((right as int32))) == (0 + to_integer((right as int32))) by {
                apply(integer::equal_add(((-1 * to_integer((right as int32))) + to_integer((left as int32))), 0, to_integer((right as int32)), to_integer((right as int32)))) using {
                    ((-1 * to_integer((right as int32))) + to_integer((left as int32))) == 0;
                    to_integer((right as int32)) == to_integer((right as int32));
                };
            }
            have to_integer((left as int32)) == ((-1 * to_integer((right as int32))) + to_integer((left as int32)) + to_integer((right as int32))) by {
                normalize();
            }
            have to_integer((right as int32)) == (0 + to_integer((right as int32))) by {
                normalize();
            }
            apply(integer::equal_substitute(((-1 * to_integer((right as int32))) + to_integer((left as int32)) + to_integer((right as int32))), (0 + to_integer((right as int32))), to_integer((left as int32)), to_integer((right as int32)))) using {
                ((-1 * to_integer((right as int32))) + to_integer((left as int32)) + to_integer((right
                    as int32))) == (0 + to_integer((right as int32)));
                to_integer((left as int32)) == ((-1 * to_integer((right as int32))) + to_integer((left
                    as int32)) + to_integer((right as int32)));
                to_integer((right as int32)) == (0 + to_integer((right as int32)));
            };
        }
        normalize() using {
            to_integer((left as int32)) == to_integer((right as int32));
        };
    }
}

theorem int32_less_equal_and_not_equal_implies_less_than(left: int32, right: int32) {
    requires left <= right;
    requires left != right;

    ensures left < right by {
        have to_integer(((left as int32) as int32)) < to_integer(((right as int32) as int32)) by {
            have not not to_integer(((left as int32) as int32)) < to_integer(((right as int32) as int32)) by {
                intro();
                have ((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as int32) as int32))) <= 0 by {
                    have to_integer(((right as int32) as int32)) <= to_integer(((left as int32) as int32)) by {
                        normalize() using {
                            not to_integer(((left as int32) as int32)) < to_integer(((right as int32) as
                                int32));
                        };
                    }
                    have ((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as int32) as int32))) == (to_integer(((right as int32) as int32)) - to_integer(((left as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer(((right as int32) as int32)), to_integer(((left as int32) as int32)), ((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as int32) as int32))))) using {
                        to_integer(((right as int32) as int32)) <= to_integer(((left as int32) as
                            int32));
                        ((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as int32) as
                            int32))) == (to_integer(((right as int32) as int32)) - to_integer(((left as
                            int32) as int32)));
                    };
                }
                have (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32)))) <= 0 by {
                    have to_integer((((left as int32) as int32) as int32)) <= to_integer((((right as int32) as int32) as int32)) by {
                        normalize() using {
                            ((left as int32) as int32) <= ((right as int32) as int32);
                        };
                    }
                    have (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32)))) == (to_integer((((left as int32) as int32) as int32)) - to_integer((((right as int32) as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference(to_integer((((left as int32) as int32) as int32)), to_integer((((right as int32) as int32) as int32)), (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32)))))) using {
                        to_integer((((left as int32) as int32) as int32)) <= to_integer((((right as
                            int32) as int32) as int32));
                        (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as
                            int32)))) == (to_integer((((left as int32) as int32) as int32)) -
                            to_integer((((right as int32) as int32) as int32)));
                    };
                }
                have (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32))) + 1) <= 0 by {
                    have to_integer((((left as int32) as int32) as int32)) <= to_integer((((right as int32) as int32) as int32)) by {
                        have (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32)))) == (to_integer((((left as int32) as int32) as int32)) - to_integer((((right as int32) as int32) as int32))) by {
                            normalize();
                        }
                        apply(click::integer::difference_le(to_integer((((left as int32) as int32) as int32)), to_integer((((right as int32) as int32) as int32)), (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32)))))) using {
                            (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32)
                                as int32)))) <= 0;
                            (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32)
                                as int32)))) == (to_integer((((left as int32) as int32) as int32)) -
                                to_integer((((right as int32) as int32) as int32)));
                        };
                    }
                    have to_integer((((left as int32) as int32) as int32)) != to_integer((((right as int32) as int32) as int32)) by {
                        normalize() using {
                            ((left as int32) as int32) != ((right as int32) as int32);
                        };
                    }
                    have to_integer((((left as int32) as int32) as int32)) < to_integer((((right as int32) as int32) as int32)) by {
                        apply(click::integer::le_ne_lt(to_integer((((left as int32) as int32) as int32)), to_integer((((right as int32) as int32) as int32)))) using {
                            to_integer((((left as int32) as int32) as int32)) <= to_integer((((right as
                                int32) as int32) as int32));
                            to_integer((((left as int32) as int32) as int32)) != to_integer((((right as
                                int32) as int32) as int32));
                        };
                    }
                    have (to_integer((((left as int32) as int32) as int32)) + 1) <= to_integer((((right as int32) as int32) as int32)) by {
                        apply(click::integer::lt_step_le(to_integer((((left as int32) as int32) as int32)), to_integer((((right as int32) as int32) as int32)))) using {
                            to_integer((((left as int32) as int32) as int32)) < to_integer((((right as
                                int32) as int32) as int32));
                        };
                    }
                    have (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32))) + 1) == ((to_integer((((left as int32) as int32) as int32)) + 1) - to_integer((((right as int32) as int32) as int32))) by {
                        normalize();
                    }
                    apply(click::integer::le_difference((to_integer((((left as int32) as int32) as int32)) + 1), to_integer((((right as int32) as int32) as int32)), (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32))) + 1))) using {
                        (to_integer((((left as int32) as int32) as int32)) + 1) <= to_integer((((right
                            as int32) as int32) as int32));
                        (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as
                            int32))) + 1) == ((to_integer((((left as int32) as int32) as int32)) + 1) -
                            to_integer((((right as int32) as int32) as int32)));
                    };
                }
                have (let integer_constant: Integer = 1; integer_constant) <= 0 by {
                    have ((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as int32) as int32)) + (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32))) + 1)) <= (0 + 0) by {
                        apply(click::integer::add_le(((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as int32) as int32))), 0, (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32))) + 1), 0)) using {
                            ((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as
                                int32) as int32))) <= 0;
                            (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32)
                                as int32))) + 1) <= 0;
                        };
                    }
                    have (let integer_constant: Integer = 1; integer_constant) == ((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as int32) as int32)) + (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32))) + 1)) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(click::integer::le_substitute(((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as int32) as int32)) + (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right as int32) as int32))) + 1)), (0 + 0), (let integer_constant: Integer = 1; integer_constant), 0)) using {
                        ((-1 * to_integer(((left as int32) as int32))) + to_integer(((right as int32) as
                            int32)) + (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right
                            as int32) as int32))) + 1)) <= (0 + 0);
                        (let integer_constant: Integer = 1; integer_constant) == ((-1 *
                            to_integer(((left as int32) as int32))) + to_integer(((right as int32) as
                            int32)) + (to_integer(((left as int32) as int32)) + (-1 * to_integer(((right
                            as int32) as int32))) + 1));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                contradiction((let integer_constant: Integer = 1; integer_constant) <= 0);
            }
            normalize() using {
                not not to_integer(((left as int32) as int32)) < to_integer(((right as int32) as
                    int32));
            };
        }
        have left < right by {
            normalize() using {
                to_integer(((left as int32) as int32)) < to_integer(((right as int32) as int32));
            };
        }
        known();
    }
}

// Wrapping unsigned arithmetic, the C operation itself. A specification that
// means C's modular result writes it with these, so it keeps that meaning
// where `+`, `-` and `*` compare exact Integers.
function uint32_wrapping_add(left: uint32, right: uint32) -> uint32 {
    left + right
}

function uint32_wrapping_sub(left: uint32, right: uint32) -> uint32 {
    left - right
}

function uint32_wrapping_mul(left: uint32, right: uint32) -> uint32 {
    left * right
}

function uint64_wrapping_add(left: uint64, right: uint64) -> uint64 {
    left + right
}

function uint64_wrapping_sub(left: uint64, right: uint64) -> uint64 {
    left - right
}

function uint64_wrapping_mul(left: uint64, right: uint64) -> uint64 {
    left * right
}

theorem uint32_add_to_integer(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have 0 <= (to_integer(left) + to_integer(right)) by {
            have 0 <= (to_integer(left) + to_integer(right)) by {
                have (-1 * to_integer(left)) <= 0 by {
                    have 0 <= to_integer(left) by {
                        normalize();
                    }
                    have (-1 * to_integer(left)) == (0 - to_integer(left)) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer(left), (-1 * to_integer(left)))) using {
                        0 <= to_integer(left);
                        (-1 * to_integer(left)) == (0 - to_integer(left));
                    };
                }
                have (-1 * to_integer(right)) <= 0 by {
                    have 0 <= to_integer(right) by {
                        normalize();
                    }
                    have (-1 * to_integer(right)) == (0 - to_integer(right)) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer(right), (-1 * to_integer(right)))) using {
                        0 <= to_integer(right);
                        (-1 * to_integer(right)) == (0 - to_integer(right));
                    };
                }
                have ((-1 * to_integer(left)) + (-1 * to_integer(right))) <= 0 by {
                    have ((-1 * to_integer(left)) + (-1 * to_integer(right))) <= (0 + 0) by {
                        apply(integer::add_le((-1 * to_integer(left)), 0, (-1 * to_integer(right)), 0)) using {
                            (-1 * to_integer(left)) <= 0;
                            (-1 * to_integer(right)) <= 0;
                        };
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute(((-1 * to_integer(left)) + (-1 * to_integer(right))), (0 + 0), ((-1 * to_integer(left)) + (-1 * to_integer(right))), 0)) using {
                        ((-1 * to_integer(left)) + (-1 * to_integer(right))) <= (0 + 0);
                        ((-1 * to_integer(left)) + (-1 * to_integer(right))) == ((-1 * to_integer(left))
                            + (-1 * to_integer(right)));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer(left)) + (-1 * to_integer(right))) == (0 - (to_integer(left) + to_integer(right))) by {
                    normalize();
                }
                apply(integer::difference_le(0, (to_integer(left) + to_integer(right)), ((-1 * to_integer(left)) + (-1 * to_integer(right))))) using {
                    ((-1 * to_integer(left)) + (-1 * to_integer(right))) <= 0;
                    ((-1 * to_integer(left)) + (-1 * to_integer(right))) == (0 - (to_integer(left) +
                        to_integer(right)));
                };
            }
            normalize() using {
                0 <= (to_integer(left) + to_integer(right));
            };
        }
        have (to_integer(left) + to_integer(right)) <= 4294967295 by {
            known();
        }
        have to_integer((left + right)) == (to_integer(left) + to_integer(right)) by {
            normalize() using {
                0 <= (to_integer(left) + to_integer(right));
                (to_integer(left) + to_integer(right)) <= 4294967295;
            };
        }
        known();
    }
}

// Exact unsigned subtraction needs the native no-underflow guard.
theorem uint32_subtract_to_integer(left: uint32, right: uint32) {
    requires right <= left;
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have 0 <= (to_integer(left) - to_integer(right)) by {
            have 0 <= (to_integer(left) - to_integer(right)) by {
                have ((-1 * to_integer(left)) + to_integer(right)) <= 0 by {
                    have ((-1 * to_integer(left)) + to_integer(right)) == (to_integer(right) - to_integer(left)) by {
                        normalize();
                    }
                    apply(integer::le_difference(to_integer(right), to_integer(left), ((-1 * to_integer(left)) + to_integer(right)))) using {
                        to_integer(right) <= to_integer(left);
                        ((-1 * to_integer(left)) + to_integer(right)) == (to_integer(right) -
                            to_integer(left));
                    };
                }
                have ((-1 * to_integer(left)) + to_integer(right)) == (0 - (to_integer(left) - to_integer(right))) by {
                    normalize();
                }
                apply(integer::difference_le(0, (to_integer(left) - to_integer(right)), ((-1 * to_integer(left)) + to_integer(right)))) using {
                    ((-1 * to_integer(left)) + to_integer(right)) <= 0;
                    ((-1 * to_integer(left)) + to_integer(right)) == (0 - (to_integer(left) -
                        to_integer(right)));
                };
            }
            normalize() using {
                0 <= (to_integer(left) - to_integer(right));
            };
        }
        have (to_integer(left) - to_integer(right)) <= 4294967295 by {
            have (to_integer(left) - to_integer(right)) <= 4294967295 by {
                have (to_integer(left) + -to_integer(4294967295u64)) <= 0 by {
                    have to_integer(left) <= 4294967295 by {
                        normalize();
                    }
                    have (to_integer(left) + -to_integer(4294967295u64)) == (to_integer(left) - 4294967295) by {
                        normalize();
                    }
                    apply(integer::le_difference(to_integer(left), 4294967295, (to_integer(left) + -to_integer(4294967295u64)))) using {
                        to_integer(left) <= 4294967295;
                        (to_integer(left) + -to_integer(4294967295u64)) == (to_integer(left) -
                            4294967295);
                    };
                }
                have (-1 * to_integer(right)) <= 0 by {
                    have 0 <= to_integer(right) by {
                        normalize();
                    }
                    have (-1 * to_integer(right)) == (0 - to_integer(right)) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer(right), (-1 * to_integer(right)))) using {
                        0 <= to_integer(right);
                        (-1 * to_integer(right)) == (0 - to_integer(right));
                    };
                }
                have (to_integer(left) + (-1 * to_integer(right)) + -to_integer(4294967295u64)) <= 0 by {
                    have (to_integer(left) + -to_integer(4294967295u64) + (-1 * to_integer(right))) <= (0 + 0) by {
                        apply(integer::add_le((to_integer(left) + -to_integer(4294967295u64)), 0, (-1 * to_integer(right)), 0)) using {
                            (to_integer(left) + -to_integer(4294967295u64)) <= 0;
                            (-1 * to_integer(right)) <= 0;
                        };
                    }
                    have (to_integer(left) + (-1 * to_integer(right)) + -to_integer(4294967295u64)) == (to_integer(left) + -to_integer(4294967295u64) + (-1 * to_integer(right))) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute((to_integer(left) + -to_integer(4294967295u64) + (-1 * to_integer(right))), (0 + 0), (to_integer(left) + (-1 * to_integer(right)) + -to_integer(4294967295u64)), 0)) using {
                        (to_integer(left) + -to_integer(4294967295u64) + (-1 * to_integer(right))) <= (0
                            + 0);
                        (to_integer(left) + (-1 * to_integer(right)) + -to_integer(4294967295u64)) ==
                            (to_integer(left) + -to_integer(4294967295u64) + (-1 * to_integer(right)));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer(left) + (-1 * to_integer(right)) + -to_integer(4294967295u64)) == ((to_integer(left) - to_integer(right)) - 4294967295) by {
                    normalize();
                }
                apply(integer::difference_le((to_integer(left) - to_integer(right)), 4294967295, (to_integer(left) + (-1 * to_integer(right)) + -to_integer(4294967295u64)))) using {
                    (to_integer(left) + (-1 * to_integer(right)) + -to_integer(4294967295u64)) <= 0;
                    (to_integer(left) + (-1 * to_integer(right)) + -to_integer(4294967295u64)) ==
                        ((to_integer(left) - to_integer(right)) - 4294967295);
                };
            }
            normalize() using {
                (to_integer(left) - to_integer(right)) <= 4294967295;
            };
        }
        have to_integer((left - right)) == (to_integer(left) - to_integer(right)) by {
            normalize() using {
                0 <= (to_integer(left) - to_integer(right));
                (to_integer(left) - to_integer(right)) <= 4294967295;
            };
        }
        known();
    }
}

theorem uint64_add_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) + to_integer(right) <= 18446744073709551615;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have 0 <= (to_integer(left) + to_integer(right)) by {
            have 0 <= (to_integer(left) + to_integer(right)) by {
                have (-1 * to_integer(left)) <= 0 by {
                    have 0 <= to_integer(left) by {
                        normalize();
                    }
                    have (-1 * to_integer(left)) == (0 - to_integer(left)) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer(left), (-1 * to_integer(left)))) using {
                        0 <= to_integer(left);
                        (-1 * to_integer(left)) == (0 - to_integer(left));
                    };
                }
                have (-1 * to_integer(right)) <= 0 by {
                    have 0 <= to_integer(right) by {
                        normalize();
                    }
                    have (-1 * to_integer(right)) == (0 - to_integer(right)) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer(right), (-1 * to_integer(right)))) using {
                        0 <= to_integer(right);
                        (-1 * to_integer(right)) == (0 - to_integer(right));
                    };
                }
                have ((-1 * to_integer(left)) + (-1 * to_integer(right))) <= 0 by {
                    have ((-1 * to_integer(left)) + (-1 * to_integer(right))) <= (0 + 0) by {
                        apply(integer::add_le((-1 * to_integer(left)), 0, (-1 * to_integer(right)), 0)) using {
                            (-1 * to_integer(left)) <= 0;
                            (-1 * to_integer(right)) <= 0;
                        };
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute(((-1 * to_integer(left)) + (-1 * to_integer(right))), (0 + 0), ((-1 * to_integer(left)) + (-1 * to_integer(right))), 0)) using {
                        ((-1 * to_integer(left)) + (-1 * to_integer(right))) <= (0 + 0);
                        ((-1 * to_integer(left)) + (-1 * to_integer(right))) == ((-1 * to_integer(left))
                            + (-1 * to_integer(right)));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer(left)) + (-1 * to_integer(right))) == (0 - (to_integer(left) + to_integer(right))) by {
                    normalize();
                }
                apply(integer::difference_le(0, (to_integer(left) + to_integer(right)), ((-1 * to_integer(left)) + (-1 * to_integer(right))))) using {
                    ((-1 * to_integer(left)) + (-1 * to_integer(right))) <= 0;
                    ((-1 * to_integer(left)) + (-1 * to_integer(right))) == (0 - (to_integer(left) +
                        to_integer(right)));
                };
            }
            normalize() using {
                0 <= (to_integer(left) + to_integer(right));
            };
        }
        have (to_integer(left) + to_integer(right)) <= 18446744073709551615 by {
            known();
        }
        have to_integer((left + right)) == (to_integer(left) + to_integer(right)) by {
            normalize() using {
                0 <= (to_integer(left) + to_integer(right));
                (to_integer(left) + to_integer(right)) <= 18446744073709551615;
            };
        }
        known();
    }
}

theorem uint64_multiply_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) * to_integer(right) <= 18446744073709551615;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by {
        have 0 <= to_integer(left) by {
            normalize();
        }
        have to_integer(left) <= 18446744073709551615 by {
            normalize();
        }
        have 0 <= to_integer(right) by {
            normalize();
        }
        have to_integer(right) <= 18446744073709551615 by {
            normalize();
        }
        have 0 <= to_integer(left) * to_integer(right) by {
            normalize() using { 0 <= to_integer(left); to_integer(left) <= 18446744073709551615; 0 <= to_integer(right); to_integer(right) <= 18446744073709551615; };
        }
        normalize() using { 0 <= to_integer(left) * to_integer(right); to_integer(left) * to_integer(right) <= 18446744073709551615; };
    }
}

theorem uint64_subtract_to_integer(left: uint64, right: uint64) {
    requires to_integer(right) <= to_integer(left);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have 0 <= (to_integer(left) - to_integer(right)) by {
            have 0 <= (to_integer(left) - to_integer(right)) by {
                have ((-1 * to_integer(left)) + to_integer(right)) <= 0 by {
                    have ((-1 * to_integer(left)) + to_integer(right)) == (to_integer(right) - to_integer(left)) by {
                        normalize();
                    }
                    apply(integer::le_difference(to_integer(right), to_integer(left), ((-1 * to_integer(left)) + to_integer(right)))) using {
                        to_integer(right) <= to_integer(left);
                        ((-1 * to_integer(left)) + to_integer(right)) == (to_integer(right) -
                            to_integer(left));
                    };
                }
                have ((-1 * to_integer(left)) + to_integer(right)) == (0 - (to_integer(left) - to_integer(right))) by {
                    normalize();
                }
                apply(integer::difference_le(0, (to_integer(left) - to_integer(right)), ((-1 * to_integer(left)) + to_integer(right)))) using {
                    ((-1 * to_integer(left)) + to_integer(right)) <= 0;
                    ((-1 * to_integer(left)) + to_integer(right)) == (0 - (to_integer(left) -
                        to_integer(right)));
                };
            }
            normalize() using {
                0 <= (to_integer(left) - to_integer(right));
            };
        }
        have (to_integer(left) - to_integer(right)) <= 18446744073709551615 by {
            have (to_integer(left) - to_integer(right)) <= 18446744073709551615 by {
                have (to_integer(left) + -to_integer(18446744073709551615u64)) <= 0 by {
                    have to_integer(left) <= 18446744073709551615 by {
                        normalize();
                    }
                    have (to_integer(left) + -to_integer(18446744073709551615u64)) == (to_integer(left) - 18446744073709551615) by {
                        normalize();
                    }
                    apply(integer::le_difference(to_integer(left), 18446744073709551615, (to_integer(left) + -to_integer(18446744073709551615u64)))) using {
                        to_integer(left) <= 18446744073709551615;
                        (to_integer(left) + -to_integer(18446744073709551615u64)) == (to_integer(left) -
                            18446744073709551615);
                    };
                }
                have (-1 * to_integer(right)) <= 0 by {
                    have 0 <= to_integer(right) by {
                        normalize();
                    }
                    have (-1 * to_integer(right)) == (0 - to_integer(right)) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer(right), (-1 * to_integer(right)))) using {
                        0 <= to_integer(right);
                        (-1 * to_integer(right)) == (0 - to_integer(right));
                    };
                }
                have (to_integer(left) + (-1 * to_integer(right)) + -to_integer(18446744073709551615u64)) <= 0 by {
                    have (to_integer(left) + -to_integer(18446744073709551615u64) + (-1 * to_integer(right))) <= (0 + 0) by {
                        apply(integer::add_le((to_integer(left) + -to_integer(18446744073709551615u64)), 0, (-1 * to_integer(right)), 0)) using {
                            (to_integer(left) + -to_integer(18446744073709551615u64)) <= 0;
                            (-1 * to_integer(right)) <= 0;
                        };
                    }
                    have (to_integer(left) + (-1 * to_integer(right)) + -to_integer(18446744073709551615u64)) == (to_integer(left) + -to_integer(18446744073709551615u64) + (-1 * to_integer(right))) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute((to_integer(left) + -to_integer(18446744073709551615u64) + (-1 * to_integer(right))), (0 + 0), (to_integer(left) + (-1 * to_integer(right)) + -to_integer(18446744073709551615u64)), 0)) using {
                        (to_integer(left) + -to_integer(18446744073709551615u64) + (-1 *
                            to_integer(right))) <= (0 + 0);
                        (to_integer(left) + (-1 * to_integer(right)) +
                            -to_integer(18446744073709551615u64)) == (to_integer(left) +
                            -to_integer(18446744073709551615u64) + (-1 * to_integer(right)));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have (to_integer(left) + (-1 * to_integer(right)) + -to_integer(18446744073709551615u64)) == ((to_integer(left) - to_integer(right)) - 18446744073709551615) by {
                    normalize();
                }
                apply(integer::difference_le((to_integer(left) - to_integer(right)), 18446744073709551615, (to_integer(left) + (-1 * to_integer(right)) + -to_integer(18446744073709551615u64)))) using {
                    (to_integer(left) + (-1 * to_integer(right)) + -to_integer(18446744073709551615u64))
                        <= 0;
                    (to_integer(left) + (-1 * to_integer(right)) + -to_integer(18446744073709551615u64))
                        == ((to_integer(left) - to_integer(right)) - 18446744073709551615);
                };
            }
            normalize() using {
                (to_integer(left) - to_integer(right)) <= 18446744073709551615;
            };
        }
        have to_integer((left - right)) == (to_integer(left) - to_integer(right)) by {
            normalize() using {
                0 <= (to_integer(left) - to_integer(right));
                (to_integer(left) - to_integer(right)) <= 18446744073709551615;
            };
        }
        known();
    }
}

theorem uint64_divide_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right));
}

theorem uint64_remainder_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}

theorem uint64_to_integer_less_equal_implies_less_equal(left: uint64, right: uint64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by known();
}

theorem uint32_pack_uint16_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high);
}

theorem uint32_pack_uint16_high_first_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer((high << 16) | low) == to_integer(low) + 65536 * to_integer(high);
}

// Exact round trips of two bounded fields packed with the high field first.
theorem uint32_unpack_uint16_low(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures (((high << 16) | low) & 65535u32) == low;
}

theorem uint32_unpack_uint16_high(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures ((((high << 16) | low) >> 16) & 65535u32) == high;
}

theorem uint64_pack_uint16_to_integer(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high);
}

// LP64 C saves the same bounded fields in a uint64 result.
theorem uint64_unpack_uint16_low(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures ((low | (high << 16)) & 65535u64) == low;
}

theorem uint64_unpack_uint16_high(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures (((low | (high << 16)) >> 16) & 65535u64) == high;
}

theorem uint64_less_than_implies_not_greater_equal(left: uint64, right: uint64) {
    requires left < right;
    ensures not (left >= right) by known();
}

// Exact observations of unsigned division require both evaluation domains.
theorem uint32_divide_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right));
}

theorem uint32_remainder_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}

theorem uint32_less_equal_to_integer(left: uint32, right: uint32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by known();
}

theorem uint32_to_integer_less_equal_implies_less_equal(left: uint32, right: uint32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by known();
}

theorem uint32_to_integer_equal_implies_equal(left: uint32, right: uint32) {
    requires to_integer(left) == to_integer(right);
    ensures left == right by known();
}

theorem uint32_to_integer_bounds(value: uint32) {
    ensures 0 <= to_integer(value) by {
        have 0u32 <= value;
        apply(integer::uint32_less_equal_to_integer(0u32, value)) using { 0u32 <= value; };
    }
    ensures to_integer(value) <= 4294967295 by {
        have value <= 4294967295u32;
        apply(integer::uint32_less_equal_to_integer(value, 4294967295u32)) using { value <= 4294967295u32; };
    }
}

theorem int32_add_to_integer(left: int32, right: int32) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have -2147483648 <= to_integer(left) + to_integer(right) by {
            known();
        }
        have to_integer(left) + to_integer(right) <= 2147483647 by {
            known();
        }
        have to_integer(left + right) == to_integer(left) + to_integer(right) by {
            normalize() using { -2147483648 <= to_integer(left) + to_integer(right); to_integer(left) + to_integer(right) <= 2147483647; };
        }
        known();
    }
}

theorem int32_less_equal_to_integer(left: int32, right: int32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by known();
}

theorem int32_to_integer_less_equal_implies_less_equal(left: int32, right: int32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by known();
}

theorem int64_to_integer_less_equal_implies_less_equal(left: int64, right: int64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by known();
}

theorem int32_subtract_to_integer(left: int32, right: int32) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have -2147483648 <= to_integer(left) - to_integer(right) by {
            known();
        }
        have to_integer(left) - to_integer(right) <= 2147483647 by {
            known();
        }
        have to_integer(left - right) == to_integer(left) - to_integer(right) by {
            normalize() using { -2147483648 <= to_integer(left) - to_integer(right); to_integer(left) - to_integer(right) <= 2147483647; };
        }
        known();
    }
}

theorem int32_remainder_to_integer(left: int32, right: int32) {
    requires defined(left % right);
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}

theorem int32_add_defined_by_integer_bounds(left: int32, right: int32) {
    requires to_integer(left) + to_integer(right) >= -2147483648;
    requires to_integer(left) + to_integer(right) <= 2147483647;
    ensures defined(left + right) by {
        known();
    }
}

theorem to_int8_round_trip(z: Integer) {
    requires z >= -128;
    requires z <= 127;
    ensures to_integer(to_int8(z)) == z by {
        have -128 <= z by {
            known();
        }
        have z <= 127 by {
            known();
        }
        normalize() using { -128 <= z; z <= 127; };
    }
}

theorem to_int16_round_trip(z: Integer) {
    requires z >= -32768;
    requires z <= 32767;
    ensures to_integer(to_int16(z)) == z by {
        have -32768 <= z by {
            known();
        }
        have z <= 32767 by {
            known();
        }
        normalize() using { -32768 <= z; z <= 32767; };
    }
}

theorem to_int32_round_trip(z: Integer) {
    requires z >= -2147483648;
    requires z <= 2147483647;
    ensures to_integer(to_int32(z)) == z by {
        have -2147483648 <= z by {
            known();
        }
        have z <= 2147483647 by {
            known();
        }
        normalize() using { -2147483648 <= z; z <= 2147483647; };
    }
}

theorem to_uint8_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 255;
    ensures to_integer(to_uint8(z)) == z by {
        have 0 <= z by {
            known();
        }
        have z <= 255 by {
            known();
        }
        normalize() using { 0 <= z; z <= 255; };
    }
}

theorem to_uint16_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 65535;
    ensures to_integer(to_uint16(z)) == z by {
        have 0 <= z by {
            known();
        }
        have z <= 65535 by {
            known();
        }
        normalize() using { 0 <= z; z <= 65535; };
    }
}

theorem to_uint32_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 4294967295;
    ensures to_integer(to_uint32(z)) == z by {
        have 0 <= z by {
            known();
        }
        have z <= 4294967295 by {
            known();
        }
        normalize() using { 0 <= z; z <= 4294967295; };
    }
}

theorem to_int64_round_trip(z: Integer) {
    requires z >= -9223372036854775808;
    requires z <= 9223372036854775807;
    ensures to_integer(to_int64(z)) == z by {
        have -9223372036854775808 <= z by {
            known();
        }
        have z <= 9223372036854775807 by {
            known();
        }
        normalize() using { -9223372036854775808 <= z; z <= 9223372036854775807; };
    }
}

theorem to_uint64_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 18446744073709551615;
    ensures to_integer(to_uint64(z)) == z by {
        have 0 <= z by {
            known();
        }
        have z <= 18446744073709551615 by {
            known();
        }
        normalize() using { 0 <= z; z <= 18446744073709551615; };
    }
}

theorem int64_subtract_to_integer(left: int64, right: int64) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have -9223372036854775808 <= to_integer(left) - to_integer(right) by {
            known();
        }
        have to_integer(left) - to_integer(right) <= 9223372036854775807 by {
            known();
        }
        have to_integer(left - right) == to_integer(left) - to_integer(right) by {
            normalize() using { -9223372036854775808 <= to_integer(left) - to_integer(right); to_integer(left) - to_integer(right) <= 9223372036854775807; };
        }
        known();
    }
}

theorem truncation_identity(n: Integer, d: Integer) {
    requires d != 0;
    ensures n == truncating_quotient(n, d) * d + truncating_remainder(n, d);
}

theorem positive_divisor_remainder_lower(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures 1 - d <= truncating_remainder(n, d);
}

theorem positive_divisor_remainder_upper(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures truncating_remainder(n, d) <= d - 1;
}

theorem nonnegative_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 <= n;
    ensures 0 <= truncating_remainder(n, d);
}

theorem nonpositive_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires n <= 0;
    ensures truncating_remainder(n, d) <= 0;
}


theorem multiply_add(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c by {
        normalize();
    }
}

theorem floor_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires r < 0 implies value == q + -1;
    requires 0 <= r implies value == q;
    ensures value * d <= n by {
        if r < 0 {
            have value == q + -1;
            apply(integer::multiply_add(q, -1, d));
            rewrite(value, q + -1);
            rewrite((q + -1) * d, q * d + -1 * d);
            solve() using { n == q * d + r; 1 - d <= r; };
        } else {
            have 0 <= r by { solve() using { not (r < 0); }; }
            have value == q;
            rewrite(value, q);
            solve() using { n == q * d + r; 0 <= r; };
        }
    }
    ensures n < (value + 1) * d by {
        if r < 0 {
            have value == q + -1;
            have value + 1 == q by { solve() using { value == q + -1; }; }
            rewrite(value + 1, q);
            solve() using { n == q * d + r; r < 0; };
        } else {
            have 0 <= r by { solve() using { not (r < 0); }; }
            have value == q;
            apply(integer::multiply_add(q, 1, d));
            rewrite(value, q);
            rewrite((q + 1) * d, q * d + 1 * d);
            solve() using { n == q * d + r; r <= d - 1; };
        }
    }
}

theorem ceiling_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires 0 < r implies value == q + 1;
    requires r <= 0 implies value == q;
    ensures n <= value * d by {
        if 0 < r {
            have value == q + 1;
            apply(integer::multiply_add(q, 1, d));
            rewrite(value, q + 1);
            rewrite((q + 1) * d, q * d + 1 * d);
            solve() using { n == q * d + r; r <= d - 1; };
        } else {
            have r <= 0 by { solve() using { not (0 < r); }; }
            have value == q;
            rewrite(value, q);
            solve() using { n == q * d + r; r <= 0; };
        }
    }
    ensures (value + -1) * d < n by {
        if 0 < r {
            have value == q + 1;
            have value + -1 == q by { solve() using { value == q + 1; }; }
            rewrite(value + -1, q);
            solve() using { n == q * d + r; 0 < r; };
        } else {
            have r <= 0 by { solve() using { not (0 < r); }; }
            have value == q;
            apply(integer::multiply_add(q, -1, d));
            rewrite(value, q);
            rewrite((q + -1) * d, q * d + -1 * d);
            solve() using { n == q * d + r; 1 - d <= r; };
        }
    }
}

theorem positive_divisor_quotient_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound * d <= n;
    ensures bound <= truncating_quotient(n, d) by {
        normalize() using { bound * d <= n; 1 <= d; };
    }
}

theorem positive_divisor_quotient_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= bound * d;
    ensures truncating_quotient(n, d) <= bound by {
        normalize() using { n <= bound * d; 1 <= d; };
    }
}

theorem positive_divisor_quotient_strict_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound < 0;
    requires bound * d < n;
    ensures bound < truncating_quotient(n, d) by {
        have bound * d <= n by { solve() using { bound * d < n; }; }
        apply(integer::positive_divisor_quotient_lower(n, d, bound));
        if bound < truncating_quotient(n, d) {
            known();
        } else {
            have truncating_quotient(n, d) == bound by { solve() using {
                bound <= truncating_quotient(n, d); not (bound < truncating_quotient(n, d));
            }; }
            if n <= 0 {
                have 0 < d by { solve() using { 1 <= d; }; }
                apply(integer::nonpositive_dividend_remainder(n, d));
                apply(integer::truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound, truncating_quotient(n, d));
                    known();
                }
                have not (bound * d < n) by { solve() using {
                    n == bound * d + truncating_remainder(n, d); truncating_remainder(n, d) <= 0;
                }; }
                contradiction(bound * d < n);
            } else {
                have 0 <= n by { solve() using { not (n <= 0); }; }
                have 0 * d <= n by { solve() using { 0 <= n; }; }
                apply(integer::positive_divisor_quotient_lower(n, d, 0));
                have not (bound < 0) by { solve() using {
                    0 <= truncating_quotient(n, d); truncating_quotient(n, d) == bound;
                }; }
                contradiction(bound < 0);
            }
        }
    }
}

theorem positive_divisor_quotient_strict_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 < bound;
    requires n < bound * d;
    ensures truncating_quotient(n, d) < bound by {
        have n <= bound * d by { solve() using { n < bound * d; }; }
        apply(integer::positive_divisor_quotient_upper(n, d, bound));
        if truncating_quotient(n, d) < bound {
            known();
        } else {
            have truncating_quotient(n, d) == bound by { solve() using {
                truncating_quotient(n, d) <= bound; not (truncating_quotient(n, d) < bound);
            }; }
            if 0 <= n {
                have 0 < d by { solve() using { 1 <= d; }; }
                apply(integer::nonnegative_dividend_remainder(n, d));
                apply(integer::truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound, truncating_quotient(n, d));
                    known();
                }
                have not (n < bound * d) by { solve() using {
                    n == bound * d + truncating_remainder(n, d); 0 <= truncating_remainder(n, d);
                }; }
                contradiction(n < bound * d);
            } else {
                have n <= 0 by { solve() using { not (0 <= n); }; }
                have n <= 0 * d by { solve() using { n <= 0; }; }
                apply(integer::positive_divisor_quotient_upper(n, d, 0));
                have not (0 < bound) by { solve() using {
                    truncating_quotient(n, d) <= 0; truncating_quotient(n, d) == bound;
                }; }
                contradiction(0 < bound);
            }
        }
    }
}

theorem lower_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, lower: Integer) {
    requires lower <= q;
    requires lower * d <= n;
    requires n == q * d + r;
    requires r < 0;
    ensures lower + 1 <= q by {
        if lower + 1 <= q {
            known();
        } else {
            have q == lower by { solve() using { lower <= q; not (lower + 1 <= q); }; }
            have n == lower * d + r by {
                rewrite(lower, q);
                known();
            }
            have not (r < 0) by { solve() using { lower * d <= n; n == lower * d + r; }; }
            contradiction(r < 0);
        }
    }
}

theorem upper_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, upper: Integer) {
    requires q <= upper;
    requires n <= upper * d;
    requires n == q * d + r;
    requires 0 < r;
    ensures q <= upper + -1 by {
        if q <= upper + -1 {
            known();
        } else {
            have q == upper by { solve() using { q <= upper; not (q <= upper + -1); }; }
            have n == upper * d + r by {
                rewrite(upper, q);
                known();
            }
            have not (0 < r) by { solve() using { n <= upper * d; n == upper * d + r; }; }
            contradiction(0 < r);
        }
    }
}
axiom multiply_order_nonnegative(a: Integer, b: Integer, factor: Integer) {
    requires a <= b;
    requires 0 <= factor;
    ensures a * factor <= b * factor;
}

theorem multiply_order_nonpositive(a: Integer, b: Integer, factor: Integer) {
    requires a <= b;
    requires factor <= 0;
    ensures b * factor <= a * factor by {
        normalize() using { a <= b; factor <= 0; };
    }
}

theorem scaled_product_bounds(value: Integer, amount: Integer, size: Integer, lower: Integer, upper: Integer) {
    requires lower <= value;
    requires value <= upper;
    requires lower <= 0;
    requires 0 <= upper;
    requires 0 <= amount;
    requires amount <= size;
    ensures lower * size <= value * amount by {
        apply(integer::multiply_order_nonnegative(lower, value, amount));
        have lower * size <= lower * amount by {
            normalize() using { amount <= size; lower <= 0; };
        }
        solve() using { lower * size <= lower * amount; lower * amount <= value * amount; };
    }
    ensures value * amount <= upper * size by {
        apply(integer::multiply_order_nonnegative(value, upper, amount));
        have upper * amount <= upper * size by {
            normalize() using { amount <= size; 0 <= upper; };
        }
        solve() using { value * amount <= upper * amount; upper * amount <= upper * size; };
    }
}

// Unsigned 32-bit product and remainder laws, proved from the division
// observations and the truncating-division lemmas above.
theorem uint32_multiply_to_integer(left: uint32, right: uint32) {
    requires right == 0u32 or left <= 4294967295u32 / right;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by {
        have 0 <= to_integer(left) by {
            normalize();
        }
        have to_integer(left) <= 4294967295 by {
            normalize();
        }
        have 0 <= to_integer(right) by {
            normalize();
        }
        have to_integer(right) <= 4294967295 by {
            normalize();
        }
        have 0 <= (to_integer(left) * to_integer(right)) by {
            normalize() using {
                0 <= to_integer(left);
                to_integer(left) <= 4294967295;
                0 <= to_integer(right);
                to_integer(right) <= 4294967295;
            };
        }
        if right == 0u32 {
            have to_integer(right) <= 0 by {
                normalize() using {
                    right == 0u32;
                };
            }
            have (to_integer(left) * to_integer(right)) <= 0 by {
                normalize() using {
                    0 <= to_integer(left);
                    to_integer(left) <= 4294967295;
                    0 <= to_integer(right);
                    to_integer(right) <= 0;
                };
            }
            have (to_integer(left) * to_integer(right)) <= 4294967295 by {
                have (to_integer(left) * to_integer(right)) <= 4294967295 by {
                    have (to_integer(left) * to_integer(right)) <= 0 by {
                        have (to_integer(left) * to_integer(right)) == ((to_integer(left) * to_integer(right)) - 0) by {
                            normalize();
                        }
                        apply(integer::le_difference((to_integer(left) * to_integer(right)), 0, (to_integer(left) * to_integer(right)))) using {
                            (to_integer(left) * to_integer(right)) <= 0;
                            (to_integer(left) * to_integer(right)) == ((to_integer(left) *
                                to_integer(right)) - 0);
                        };
                    }
                    have (let integer_constant: Integer = -to_integer(4294967295u64); integer_constant) <= 0 by {
                        normalize();
                    }
                    have ((to_integer(left) * to_integer(right)) + -to_integer(4294967295u64)) <= 0 by {
                        have ((to_integer(left) * to_integer(right)) + (let integer_constant: Integer = -to_integer(4294967295u64); integer_constant)) <= (0 + 0) by {
                            apply(integer::add_le((to_integer(left) * to_integer(right)), 0, (let integer_constant: Integer = -to_integer(4294967295u64); integer_constant), 0)) using {
                                (to_integer(left) * to_integer(right)) <= 0;
                                (let integer_constant: Integer = -to_integer(4294967295u64);
                                    integer_constant) <= 0;
                            };
                        }
                        have ((to_integer(left) * to_integer(right)) + -to_integer(4294967295u64)) == ((to_integer(left) * to_integer(right)) + (let integer_constant: Integer = -to_integer(4294967295u64); integer_constant)) by {
                            normalize();
                        }
                        have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                            normalize();
                        }
                        apply(integer::le_substitute(((to_integer(left) * to_integer(right)) + (let integer_constant: Integer = -to_integer(4294967295u64); integer_constant)), (0 + 0), ((to_integer(left) * to_integer(right)) + -to_integer(4294967295u64)), 0)) using {
                            ((to_integer(left) * to_integer(right)) + (let integer_constant: Integer =
                                -to_integer(4294967295u64); integer_constant)) <= (0 + 0);
                            ((to_integer(left) * to_integer(right)) + -to_integer(4294967295u64)) ==
                                ((to_integer(left) * to_integer(right)) + (let integer_constant: Integer
                                = -to_integer(4294967295u64); integer_constant));
                            (let integer_value: Integer = 0; integer_value) == (0 + 0);
                        };
                    }
                    have ((to_integer(left) * to_integer(right)) + -to_integer(4294967295u64)) == ((to_integer(left) * to_integer(right)) - 4294967295) by {
                        normalize();
                    }
                    apply(integer::difference_le((to_integer(left) * to_integer(right)), 4294967295, ((to_integer(left) * to_integer(right)) + -to_integer(4294967295u64)))) using {
                        ((to_integer(left) * to_integer(right)) + -to_integer(4294967295u64)) <= 0;
                        ((to_integer(left) * to_integer(right)) + -to_integer(4294967295u64)) ==
                            ((to_integer(left) * to_integer(right)) - 4294967295);
                    };
                }
                normalize() using {
                    (to_integer(left) * to_integer(right)) <= 4294967295;
                };
            }
            normalize() using {
                0 <= (to_integer(left) * to_integer(right));
                (to_integer(left) * to_integer(right)) <= 4294967295;
            };
        } else {
            have left <= ((4294967295u32 / right) as uint32) by {
                cases {
                    right == 0u32 => {
                        contradiction(right == 0u32);
                    }
                    left <= ((4294967295u32 / right) as uint32) => {
                        known();
                    }
                }
            }
            have right != 0u32 by {
                normalize() using {
                    not right == 0u32;
                };
            }
            have 1 <= to_integer(right) by {
                have 1 <= to_integer(right) by {
                    have ((-1 * to_integer(right)) + 1) <= 0 by {
                        have (-1 * to_integer(right)) <= 0 by {
                            have 0 <= to_integer(right) by {
                                normalize();
                            }
                            have (-1 * to_integer(right)) == (0 - to_integer(right)) by {
                                normalize();
                            }
                            apply(integer::le_difference(0, to_integer(right), (-1 * to_integer(right)))) using {
                                0 <= to_integer(right);
                                (-1 * to_integer(right)) == (0 - to_integer(right));
                            };
                        }
                        have 0 <= to_integer(right) by {
                            have (-1 * to_integer(right)) == (0 - to_integer(right)) by {
                                normalize();
                            }
                            apply(integer::difference_le(0, to_integer(right), (-1 * to_integer(right)))) using {
                                (-1 * to_integer(right)) <= 0;
                                (-1 * to_integer(right)) == (0 - to_integer(right));
                            };
                        }
                        have 0 != to_integer(right) by {
                            normalize() using {
                                to_integer(right) != 0;
                            };
                        }
                        have 0 < to_integer(right) by {
                            apply(integer::le_ne_lt(0, to_integer(right))) using {
                                0 <= to_integer(right);
                                0 != to_integer(right);
                            };
                        }
                        have (0 + 1) <= to_integer(right) by {
                            apply(integer::lt_step_le(0, to_integer(right))) using {
                                0 < to_integer(right);
                            };
                        }
                        have ((-1 * to_integer(right)) + 1) == ((0 + 1) - to_integer(right)) by {
                            normalize();
                        }
                        apply(integer::le_difference((0 + 1), to_integer(right), ((-1 * to_integer(right)) + 1))) using {
                            (0 + 1) <= to_integer(right);
                            ((-1 * to_integer(right)) + 1) == ((0 + 1) - to_integer(right));
                        };
                    }
                    have ((-1 * to_integer(right)) + 1) == (1 - to_integer(right)) by {
                        normalize();
                    }
                    apply(integer::difference_le(1, to_integer(right), ((-1 * to_integer(right)) + 1))) using {
                        ((-1 * to_integer(right)) + 1) <= 0;
                        ((-1 * to_integer(right)) + 1) == (1 - to_integer(right));
                    };
                }
                normalize() using {
                    1 <= to_integer(right);
                };
            }
            apply(integer::uint32_divide_to_integer(4294967295u32, right)) using {
                right != 0u32;
                to_integer(right) != 0;
            };
            apply(integer::truncation_identity(4294967295, to_integer(right))) using {
                to_integer(right) != 0;
            };
            apply(integer::nonnegative_dividend_remainder(4294967295, to_integer(right))) using {
                to_integer(right) != 0;
            };
            have 0 <= (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) by {
                have to_integer(left) <= truncating_quotient(4294967295, to_integer(right)) by { rewrite(truncating_quotient(4294967295, to_integer(right)), to_integer(4294967295u32 / right)); known(); }
                have to_integer(left) + -to_integer(left) <= truncating_quotient(4294967295, to_integer(right)) + -to_integer(left) by {
                    apply(integer::add_le(to_integer(left), truncating_quotient(4294967295, to_integer(right)), -to_integer(left), -to_integer(left))) using { to_integer(left) <= truncating_quotient(4294967295, to_integer(right)); -to_integer(left) <= -to_integer(left); to_integer(right) != 0; };
                }
                have 0 == to_integer(left) + -to_integer(left) by normalize();
                have truncating_quotient(4294967295, to_integer(right)) - to_integer(left) == truncating_quotient(4294967295, to_integer(right)) + -to_integer(left) by normalize();
                apply(integer::le_substitute(to_integer(left) + -to_integer(left), truncating_quotient(4294967295, to_integer(right)) + -to_integer(left), 0, truncating_quotient(4294967295, to_integer(right)) - to_integer(left))) using {
                    to_integer(left) + -to_integer(left) <= truncating_quotient(4294967295, to_integer(right)) + -to_integer(left); 0 == to_integer(left) + -to_integer(left); truncating_quotient(4294967295, to_integer(right)) - to_integer(left) == truncating_quotient(4294967295, to_integer(right)) + -to_integer(left); to_integer(right) != 0;
                };
            }
            have (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) <= 4294967295 by {
                have truncating_quotient(4294967295, to_integer(right)) <= 4294967295 by { rewrite(truncating_quotient(4294967295, to_integer(right)), to_integer(4294967295u32 / right)); normalize(); }
                have -to_integer(left) <= 0 by {
                    have -to_integer(left) == 0 - to_integer(left) by normalize();
                    apply(integer::le_difference(0, to_integer(left), -to_integer(left))) using { 0 <= to_integer(left); -to_integer(left) == 0 - to_integer(left); };
                }
                have truncating_quotient(4294967295, to_integer(right)) + -to_integer(left) <= 4294967295 + 0 by {
                    apply(integer::add_le(truncating_quotient(4294967295, to_integer(right)), 4294967295, -to_integer(left), 0)) using { truncating_quotient(4294967295, to_integer(right)) <= 4294967295; -to_integer(left) <= 0; to_integer(right) != 0; };
                }
                have truncating_quotient(4294967295, to_integer(right)) - to_integer(left) == truncating_quotient(4294967295, to_integer(right)) + -to_integer(left) by normalize();
                have 4294967295 == 4294967295 + 0 by normalize();
                apply(integer::le_substitute(truncating_quotient(4294967295, to_integer(right)) + -to_integer(left), 4294967295 + 0, truncating_quotient(4294967295, to_integer(right)) - to_integer(left), 4294967295)) using {
                    truncating_quotient(4294967295, to_integer(right)) + -to_integer(left) <= 4294967295 + 0; truncating_quotient(4294967295, to_integer(right)) - to_integer(left) == truncating_quotient(4294967295, to_integer(right)) + -to_integer(left); 4294967295 == 4294967295 + 0; to_integer(right) != 0;
                };
            }
            have 0 <= ((truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right)) by {
                normalize() using {
                    0 <= (truncating_quotient(4294967295, to_integer(right)) - to_integer(left));
                    (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) <=
                        4294967295;
                    0 <= to_integer(right);
                    to_integer(right) <= 4294967295;
                };
            }
            have ((truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right)) == ((truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) - (to_integer(left) * to_integer(right))) by {
                normalize();
            }
            have (to_integer(left) * to_integer(right)) <= 4294967295 by {
                have 0 + (to_integer(left) * to_integer(right)) <= ((truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right)) + (to_integer(left) * to_integer(right)) by {
                    apply(integer::add_le(0, ((truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right)), (to_integer(left) * to_integer(right)), (to_integer(left) * to_integer(right)))) using { 0 <= ((truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right)); (to_integer(left) * to_integer(right)) <= (to_integer(left) * to_integer(right)); to_integer(right) != 0; };
                }
                have (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) == ((truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right)) + (to_integer(left) * to_integer(right)) by { rewrite(((truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right)), (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) - (to_integer(left) * to_integer(right))); normalize(); }
                have (to_integer(left) * to_integer(right)) <= (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) by {
                    have (to_integer(left) * to_integer(right)) == 0 + (to_integer(left) * to_integer(right)) by normalize();
                    apply(integer::le_substitute(0 + (to_integer(left) * to_integer(right)), ((truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right)) + (to_integer(left) * to_integer(right)), (to_integer(left) * to_integer(right)), (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)))) using {
                        0 + (to_integer(left) * to_integer(right)) <= ((truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right)) + (to_integer(left) * to_integer(right)); (to_integer(left) * to_integer(right)) == 0 + (to_integer(left) * to_integer(right)); (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) == ((truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right)) + (to_integer(left) * to_integer(right)); to_integer(right) != 0;
                    };
                }
                have (to_integer(left) * to_integer(right)) + 0 <= (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + truncating_remainder(4294967295, to_integer(right)) by {
                    apply(integer::add_le((to_integer(left) * to_integer(right)), (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)), 0, truncating_remainder(4294967295, to_integer(right)))) using { (to_integer(left) * to_integer(right)) <= (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)); 0 <= truncating_remainder(4294967295, to_integer(right)); to_integer(right) != 0; };
                }
                have (to_integer(left) * to_integer(right)) == (to_integer(left) * to_integer(right)) + 0 by normalize();
                apply(integer::le_substitute((to_integer(left) * to_integer(right)) + 0, (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + truncating_remainder(4294967295, to_integer(right)), (to_integer(left) * to_integer(right)), 4294967295)) using {
                    (to_integer(left) * to_integer(right)) + 0 <= (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + truncating_remainder(4294967295, to_integer(right)); (to_integer(left) * to_integer(right)) == (to_integer(left) * to_integer(right)) + 0; 4294967295 == (truncating_quotient(4294967295, to_integer(right)) * to_integer(right)) + truncating_remainder(4294967295, to_integer(right)); to_integer(right) != 0;
                };
            }
            normalize() using {
                0 <= (to_integer(left) * to_integer(right));
                (to_integer(left) * to_integer(right)) <= 4294967295;
            };
        }
    }
}

theorem uint32_multiply_guard_by_integer_bound(left: uint32, right: uint32) {
    requires to_integer(left) * to_integer(right) <= 4294967295;
    ensures right == 0u32 or left <= 4294967295u32 / right by {
        if right == 0u32 {
            known();
        } else {
            have right != 0u32 by {
                normalize() using {
                    not right == 0u32;
                };
            }
            have 1 <= to_integer(right) by {
                have 1 <= to_integer(right) by {
                    have ((-1 * to_integer(right)) + 1) <= 0 by {
                        have (-1 * to_integer(right)) <= 0 by {
                            have 0 <= to_integer(right) by {
                                normalize();
                            }
                            have (-1 * to_integer(right)) == (0 - to_integer(right)) by {
                                normalize();
                            }
                            apply(integer::le_difference(0, to_integer(right), (-1 * to_integer(right)))) using {
                                0 <= to_integer(right);
                                (-1 * to_integer(right)) == (0 - to_integer(right));
                            };
                        }
                        have 0 <= to_integer(right) by {
                            have (-1 * to_integer(right)) == (0 - to_integer(right)) by {
                                normalize();
                            }
                            apply(integer::difference_le(0, to_integer(right), (-1 * to_integer(right)))) using {
                                (-1 * to_integer(right)) <= 0;
                                (-1 * to_integer(right)) == (0 - to_integer(right));
                            };
                        }
                        have 0 != to_integer(right) by {
                            normalize() using {
                                to_integer(right) != 0;
                            };
                        }
                        have 0 < to_integer(right) by {
                            apply(integer::le_ne_lt(0, to_integer(right))) using {
                                0 <= to_integer(right);
                                0 != to_integer(right);
                            };
                        }
                        have (0 + 1) <= to_integer(right) by {
                            apply(integer::lt_step_le(0, to_integer(right))) using {
                                0 < to_integer(right);
                            };
                        }
                        have ((-1 * to_integer(right)) + 1) == ((0 + 1) - to_integer(right)) by {
                            normalize();
                        }
                        apply(integer::le_difference((0 + 1), to_integer(right), ((-1 * to_integer(right)) + 1))) using {
                            (0 + 1) <= to_integer(right);
                            ((-1 * to_integer(right)) + 1) == ((0 + 1) - to_integer(right));
                        };
                    }
                    have ((-1 * to_integer(right)) + 1) == (1 - to_integer(right)) by {
                        normalize();
                    }
                    apply(integer::difference_le(1, to_integer(right), ((-1 * to_integer(right)) + 1))) using {
                        ((-1 * to_integer(right)) + 1) <= 0;
                        ((-1 * to_integer(right)) + 1) == (1 - to_integer(right));
                    };
                }
                normalize() using {
                    1 <= to_integer(right);
                };
            }
            apply(integer::positive_divisor_quotient_lower(4294967295, to_integer(right), to_integer(left))) using {
                to_integer(right) != 0;
                1 <= to_integer(right);
                (to_integer(left) * to_integer(right)) <= 4294967295;
            };
            apply(integer::uint32_divide_to_integer(4294967295u32, right)) using {
                right != 0u32;
                to_integer(right) != 0;
            };
            have to_integer(left) <= to_integer((4294967295u32 / right)) by {
                known();
            }
            have left <= (4294967295u32 / right) as uint32 by {
                normalize() using {
                    to_integer(left) <= to_integer((4294967295u32 / right));
                };
            }
            known();
        }
    }
}

theorem uint32_remainder_less_than_divisor(value: uint32, divisor: uint32) {
    requires divisor != 0u32;
    ensures value % divisor < divisor by {
        have to_integer(divisor) != 0 by normalize() using { divisor != 0u32; };
        have 0 <= to_integer(divisor) by normalize();
        have 0 < to_integer(divisor) by {
            apply(integer::le_ne_lt(0, to_integer(divisor))) using { 0 <= to_integer(divisor); 0 != to_integer(divisor); };
        }
        apply(integer::uint32_remainder_to_integer(value, divisor)) using { divisor != 0u32; to_integer(divisor) != 0; };
        apply(integer::positive_divisor_remainder_upper(to_integer(value), to_integer(divisor))) using { to_integer(divisor) != 0; 0 < to_integer(divisor); };
        have truncating_remainder(to_integer(value), to_integer(divisor)) + 1 <= (to_integer(divisor) - 1) + 1 by {
            apply(integer::add_le(truncating_remainder(to_integer(value), to_integer(divisor)), to_integer(divisor) - 1, 1, 1)) using { truncating_remainder(to_integer(value), to_integer(divisor)) <= to_integer(divisor) - 1; 1 <= 1; to_integer(divisor) != 0; };
        }
        have truncating_remainder(to_integer(value), to_integer(divisor)) + 1 <= to_integer(divisor) by {
            have to_integer(divisor) == (to_integer(divisor) - 1) + 1 by normalize();
            apply(integer::le_substitute(truncating_remainder(to_integer(value), to_integer(divisor)) + 1, (to_integer(divisor) - 1) + 1, truncating_remainder(to_integer(value), to_integer(divisor)) + 1, to_integer(divisor))) using {
                truncating_remainder(to_integer(value), to_integer(divisor)) + 1 <= (to_integer(divisor) - 1) + 1; truncating_remainder(to_integer(value), to_integer(divisor)) + 1 == truncating_remainder(to_integer(value), to_integer(divisor)) + 1; to_integer(divisor) == (to_integer(divisor) - 1) + 1; to_integer(divisor) != 0;
            };
        }
        have to_integer(value % divisor) + 1 == truncating_remainder(to_integer(value), to_integer(divisor)) + 1 by {
            apply(integer::equal_add(to_integer(value % divisor), truncating_remainder(to_integer(value), to_integer(divisor)), 1, 1)) using { to_integer(value % divisor) == truncating_remainder(to_integer(value), to_integer(divisor)); 1 == 1; divisor != 0u32; to_integer(divisor) != 0; };
        }
        have to_integer(value % divisor) + 1 <= to_integer(divisor) by {
            apply(integer::le_substitute(truncating_remainder(to_integer(value), to_integer(divisor)) + 1, to_integer(divisor), to_integer(value % divisor) + 1, to_integer(divisor))) using {
                truncating_remainder(to_integer(value), to_integer(divisor)) + 1 <= to_integer(divisor); to_integer(value % divisor) + 1 == truncating_remainder(to_integer(value), to_integer(divisor)) + 1; to_integer(divisor) == to_integer(divisor); divisor != 0u32; to_integer(divisor) != 0;
            };
        }
        apply(integer::step_le_lt(to_integer(value % divisor), to_integer(divisor))) using { to_integer(value % divisor) + 1 <= to_integer(divisor); divisor != 0u32; to_integer(divisor) != 0; };
    }
}

theorem uint32_less_than_divisor_implies_remainder_is_value(value: uint32, divisor: uint32) {
    requires value < divisor;
    ensures value % divisor == value by {
        have to_integer(value) < to_integer(divisor) by {
            normalize() using {
                value < divisor;
            };
        }
        have 0 <= to_integer(value) by {
            normalize();
        }
        have 1 <= to_integer(divisor) by {
            have 1 <= to_integer(divisor) by {
                have (to_integer(value) + (-1 * to_integer(divisor)) + 1) <= 0 by {
                    have (to_integer(value) + 1) <= to_integer(divisor) by {
                        apply(integer::lt_step_le(to_integer(value), to_integer(divisor))) using {
                            to_integer(value) < to_integer(divisor);
                        };
                    }
                    have (to_integer(value) + (-1 * to_integer(divisor)) + 1) == ((to_integer(value) + 1) - to_integer(divisor)) by {
                        normalize();
                    }
                    apply(integer::le_difference((to_integer(value) + 1), to_integer(divisor), (to_integer(value) + (-1 * to_integer(divisor)) + 1))) using {
                        (to_integer(value) + 1) <= to_integer(divisor);
                        (to_integer(value) + (-1 * to_integer(divisor)) + 1) == ((to_integer(value) + 1)
                            - to_integer(divisor));
                    };
                }
                have (-1 * to_integer(value)) <= 0 by {
                    have 0 <= to_integer(value) by {
                        normalize();
                    }
                    have (-1 * to_integer(value)) == (0 - to_integer(value)) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer(value), (-1 * to_integer(value)))) using {
                        0 <= to_integer(value);
                        (-1 * to_integer(value)) == (0 - to_integer(value));
                    };
                }
                have ((-1 * to_integer(divisor)) + 1) <= 0 by {
                    have (to_integer(value) + (-1 * to_integer(divisor)) + 1 + (-1 * to_integer(value))) <= (0 + 0) by {
                        apply(integer::add_le((to_integer(value) + (-1 * to_integer(divisor)) + 1), 0, (-1 * to_integer(value)), 0)) using {
                            (to_integer(value) + (-1 * to_integer(divisor)) + 1) <= 0;
                            (-1 * to_integer(value)) <= 0;
                        };
                    }
                    have ((-1 * to_integer(divisor)) + 1) == (to_integer(value) + (-1 * to_integer(divisor)) + 1 + (-1 * to_integer(value))) by {
                        normalize();
                    }
                    have (let integer_value: Integer = 0; integer_value) == (0 + 0) by {
                        normalize();
                    }
                    apply(integer::le_substitute((to_integer(value) + (-1 * to_integer(divisor)) + 1 + (-1 * to_integer(value))), (0 + 0), ((-1 * to_integer(divisor)) + 1), 0)) using {
                        (to_integer(value) + (-1 * to_integer(divisor)) + 1 + (-1 * to_integer(value)))
                            <= (0 + 0);
                        ((-1 * to_integer(divisor)) + 1) == (to_integer(value) + (-1 *
                            to_integer(divisor)) + 1 + (-1 * to_integer(value)));
                        (let integer_value: Integer = 0; integer_value) == (0 + 0);
                    };
                }
                have ((-1 * to_integer(divisor)) + 1) == (1 - to_integer(divisor)) by {
                    normalize();
                }
                apply(integer::difference_le(1, to_integer(divisor), ((-1 * to_integer(divisor)) + 1))) using {
                    ((-1 * to_integer(divisor)) + 1) <= 0;
                    ((-1 * to_integer(divisor)) + 1) == (1 - to_integer(divisor));
                };
            }
            normalize() using {
                1 <= to_integer(divisor);
            };
        }
        have to_integer(divisor) != 0 by {
            normalize() using {
                1 <= to_integer(divisor);
            };
        }
        have divisor != 0u32 by {
            normalize() using {
                to_integer(divisor) != 0;
            };
        }
        apply(integer::uint32_remainder_to_integer(value, divisor)) using {
            divisor != 0u32;
            to_integer(divisor) != 0;
        };
        have (0 * to_integer(divisor)) <= to_integer(value) by {
            have (0 * to_integer(divisor)) <= to_integer(value) by {
                have (-1 * to_integer(value)) <= 0 by {
                    have (-1 * to_integer(value)) == (0 - to_integer(value)) by {
                        normalize();
                    }
                    apply(integer::le_difference(0, to_integer(value), (-1 * to_integer(value)))) using {
                        0 <= to_integer(value);
                        (-1 * to_integer(value)) == (0 - to_integer(value));
                    };
                }
                have (-1 * to_integer(value)) == ((0 * to_integer(divisor)) - to_integer(value)) by {
                    normalize();
                }
                apply(integer::difference_le((0 * to_integer(divisor)), to_integer(value), (-1 * to_integer(value)))) using {
                    (-1 * to_integer(value)) <= 0;
                    (-1 * to_integer(value)) == ((0 * to_integer(divisor)) - to_integer(value));
                };
            }
            normalize() using {
                (0 * to_integer(divisor)) <= to_integer(value);
            };
        }
        apply(integer::positive_divisor_quotient_lower(to_integer(value), to_integer(divisor), 0)) using {
            to_integer(divisor) != 0;
            1 <= to_integer(divisor);
            (0 * to_integer(divisor)) <= to_integer(value);
        };
        have to_integer(value) < (1 * to_integer(divisor)) by {
            have to_integer(value) < (1 * to_integer(divisor)) by {
                have (to_integer(value) + (-1 * to_integer(divisor)) + 1) <= 0 by {
                    have (to_integer(value) + 1) <= to_integer(divisor) by {
                        apply(integer::lt_step_le(to_integer(value), to_integer(divisor))) using {
                            to_integer(value) < to_integer(divisor);
                        };
                    }
                    have (to_integer(value) + (-1 * to_integer(divisor)) + 1) == ((to_integer(value) + 1) - to_integer(divisor)) by {
                        normalize();
                    }
                    apply(integer::le_difference((to_integer(value) + 1), to_integer(divisor), (to_integer(value) + (-1 * to_integer(divisor)) + 1))) using {
                        (to_integer(value) + 1) <= to_integer(divisor);
                        (to_integer(value) + (-1 * to_integer(divisor)) + 1) == ((to_integer(value) + 1)
                            - to_integer(divisor));
                    };
                }
                have (to_integer(value) + (-1 * to_integer(divisor)) + 1) == ((to_integer(value) + 1) - (1 * to_integer(divisor))) by {
                    normalize();
                }
                apply(integer::difference_le((to_integer(value) + 1), (1 * to_integer(divisor)), (to_integer(value) + (-1 * to_integer(divisor)) + 1))) using {
                    (to_integer(value) + (-1 * to_integer(divisor)) + 1) <= 0;
                    (to_integer(value) + (-1 * to_integer(divisor)) + 1) == ((to_integer(value) + 1) -
                        (1 * to_integer(divisor)));
                };
                apply(integer::step_le_lt(to_integer(value), (1 * to_integer(divisor)))) using {
                    (to_integer(value) + 1) <= (1 * to_integer(divisor));
                };
            }
            normalize() using {
                to_integer(value) < (1 * to_integer(divisor));
            };
        }
        have 0 < 1 by {
            normalize();
        }
        apply(integer::positive_divisor_quotient_strict_upper(to_integer(value), to_integer(divisor), 1)) using {
            to_integer(divisor) != 0;
            1 <= to_integer(divisor);
            0 < 1;
            to_integer(value) < (1 * to_integer(divisor));
        };
        have truncating_quotient(to_integer(value), to_integer(divisor)) == 0 by {
            have truncating_quotient(to_integer(value), to_integer(divisor)) + 1 <= 1 by {
                apply(integer::lt_step_le(truncating_quotient(to_integer(value), to_integer(divisor)), 1)) using { truncating_quotient(to_integer(value), to_integer(divisor)) < 1; to_integer(divisor) != 0; };
            }
            have truncating_quotient(to_integer(value), to_integer(divisor)) <= 0 by {
                have truncating_quotient(to_integer(value), to_integer(divisor)) == (truncating_quotient(to_integer(value), to_integer(divisor)) + 1) - 1 by normalize();
                apply(integer::le_difference(truncating_quotient(to_integer(value), to_integer(divisor)) + 1, 1, truncating_quotient(to_integer(value), to_integer(divisor)))) using { truncating_quotient(to_integer(value), to_integer(divisor)) + 1 <= 1; truncating_quotient(to_integer(value), to_integer(divisor)) == (truncating_quotient(to_integer(value), to_integer(divisor)) + 1) - 1; to_integer(divisor) != 0; };
            }
            apply(integer::le_antisymmetric(truncating_quotient(to_integer(value), to_integer(divisor)), 0)) using { truncating_quotient(to_integer(value), to_integer(divisor)) <= 0; 0 <= truncating_quotient(to_integer(value), to_integer(divisor)); to_integer(divisor) != 0; };
        }
        apply(integer::truncation_identity(to_integer(value), to_integer(divisor))) using {
            to_integer(divisor) != 0;
        };
        have (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) == 0 by {
            rewrite(truncating_quotient(to_integer(value), to_integer(divisor)), 0);
            normalize();
        }
        have to_integer((value % divisor)) == to_integer(value) by {
            have (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)) == 0 + truncating_remainder(to_integer(value), to_integer(divisor)) by {
                apply(integer::equal_add((truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)), 0, truncating_remainder(to_integer(value), to_integer(divisor)), truncating_remainder(to_integer(value), to_integer(divisor)))) using { (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) == 0; truncating_remainder(to_integer(value), to_integer(divisor)) == truncating_remainder(to_integer(value), to_integer(divisor)); to_integer(divisor) != 0; };
            }
            have truncating_remainder(to_integer(value), to_integer(divisor)) == 0 + truncating_remainder(to_integer(value), to_integer(divisor)) by normalize();
            have (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)) == truncating_remainder(to_integer(value), to_integer(divisor)) by {
                apply(integer::equal_substitute((truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)), 0 + truncating_remainder(to_integer(value), to_integer(divisor)), (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)), truncating_remainder(to_integer(value), to_integer(divisor)))) using {
                    (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)) == 0 + truncating_remainder(to_integer(value), to_integer(divisor)); (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)) == (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)); truncating_remainder(to_integer(value), to_integer(divisor)) == 0 + truncating_remainder(to_integer(value), to_integer(divisor)); to_integer(divisor) != 0;
                };
            }
            have to_integer(value) == truncating_remainder(to_integer(value), to_integer(divisor)) by {
                apply(integer::equal_substitute((truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)), truncating_remainder(to_integer(value), to_integer(divisor)), to_integer(value), truncating_remainder(to_integer(value), to_integer(divisor)))) using {
                    (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)) == truncating_remainder(to_integer(value), to_integer(divisor)); to_integer(value) == (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) + truncating_remainder(to_integer(value), to_integer(divisor)); truncating_remainder(to_integer(value), to_integer(divisor)) == truncating_remainder(to_integer(value), to_integer(divisor)); to_integer(divisor) != 0;
                };
            }
            apply(integer::equal_substitute(truncating_remainder(to_integer(value), to_integer(divisor)), truncating_remainder(to_integer(value), to_integer(divisor)), to_integer(value % divisor), to_integer(value))) using {
                truncating_remainder(to_integer(value), to_integer(divisor)) == truncating_remainder(to_integer(value), to_integer(divisor)); to_integer(value % divisor) == truncating_remainder(to_integer(value), to_integer(divisor)); to_integer(value) == truncating_remainder(to_integer(value), to_integer(divisor)); divisor != 0u32; to_integer(divisor) != 0;
            };
        }
        known();
    }
}

// A native nonzero quotient guard bounds the exact Integer product.
theorem uint64_product_bound_from_division(x: uint64, y: uint64) {
    requires y != 0u64;
    requires x <= 18446744073709551615u64 / y;
    ensures to_integer(x) * to_integer(y) <= to_integer(18446744073709551615u64) by {
        have to_integer(y) != 0;
        have 0 <= to_integer(y);
        have 0 <= to_integer(18446744073709551615u64) by normalize();
        apply(integer::uint64_divide_to_integer(18446744073709551615u64, y)) using {
            y != 0u64;
            to_integer(y) != 0;
        };
        have to_integer(x) <= to_integer(18446744073709551615u64 / y);
        apply(integer::multiply_order_nonnegative(to_integer(x), to_integer(18446744073709551615u64 / y), to_integer(y))) using {
            to_integer(x) <= to_integer(18446744073709551615u64 / y);
            0 <= to_integer(y);
            y != 0u64;
        };
        apply(integer::truncation_identity(to_integer(18446744073709551615u64), to_integer(y))) using { to_integer(y) != 0; };
        apply(integer::nonnegative_dividend_remainder(to_integer(18446744073709551615u64), to_integer(y))) using {
            to_integer(y) != 0;
            0 <= to_integer(18446744073709551615u64);
        };
        have to_integer(18446744073709551615u64 / y) * to_integer(y) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y) by {
            rewrite(to_integer(18446744073709551615u64 / y), truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)));
            normalize();
        }
        solve() using {
            to_integer(x) * to_integer(y) <= to_integer(18446744073709551615u64 / y) * to_integer(y);
            to_integer(18446744073709551615u64 / y) * to_integer(y) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y);
            to_integer(18446744073709551615u64) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y) + truncating_remainder(to_integer(18446744073709551615u64), to_integer(y));
            0 <= truncating_remainder(to_integer(18446744073709551615u64), to_integer(y));
        };
    }
}

// Representation bytes of one readable unsigned word, at the current point.
theorem uint32_from_le_bytes(p: uint32*) {
    requires little_endian();
    views p[0..1];
    requires defined(p[0]);
    ensures p[0] ==
        (((p as (uint8 *))[0] as uint32) |
         ((p as (uint8 *))[1] as uint32) << 8u32 |
         ((p as (uint8 *))[2] as uint32) << 16u32 |
         ((p as (uint8 *))[3] as uint32) << 24u32);
}
