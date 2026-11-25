//! Retained Integer quotient/remainder proofs from selected scalar bounds.
use super::*;
use crate::kernel::{IntegerTerm as I, SharedIntegerTerm};

fn c(n: &BigInt) -> SyntaxTerm {
    surface_signed_integer_literal(n)
}
fn lit(n: i64) -> SyntaxTerm {
    c(&BigInt::from(n))
}
fn neg(a: SyntaxTerm) -> SyntaxTerm {
    SyntaxTerm::Negate(Box::new(a))
}
fn add(a: SyntaxTerm, b: SyntaxTerm) -> SyntaxTerm {
    SyntaxTerm::Add(Box::new(a), Box::new(b))
}
fn sub(a: SyntaxTerm, b: SyntaxTerm) -> SyntaxTerm {
    SyntaxTerm::Subtract(Box::new(a), Box::new(b))
}
fn mul(a: SyntaxTerm, b: SyntaxTerm) -> SyntaxTerm {
    SyntaxTerm::Multiply(Box::new(a), Box::new(b))
}
fn compare(a: SyntaxTerm, operator: ComparisonOperator, b: SyntaxTerm) -> SyntaxProposition {
    fn numerical(expression: &SyntaxTerm) -> bool {
        match expression {
            SyntaxTerm::IntegerLiteral(_) => true,
            SyntaxTerm::Negate(a) => numerical(a),
            SyntaxTerm::Add(a, b) | SyntaxTerm::Subtract(a, b) | SyntaxTerm::Multiply(a, b) => {
                numerical(a) && numerical(b)
            }
            _ => false,
        }
    }
    let integer_context = numerical(&a) && numerical(&b);
    SyntaxProposition::Comparison {
        left: if integer_context {
            super::super::surface_synthesis::integer_typed_expression(a)
        } else {
            a
        },
        operator,
        right: b,
    }
}
fn le(a: SyntaxTerm, b: SyntaxTerm) -> SyntaxProposition {
    compare(a, ComparisonOperator::LessEqual, b)
}
fn eq(a: SyntaxTerm, b: SyntaxTerm) -> SyntaxProposition {
    compare(a, ComparisonOperator::Equal, b)
}
fn ne(a: SyntaxTerm, b: SyntaxTerm) -> SyntaxProposition {
    compare(a, ComparisonOperator::NotEqual, b)
}
fn operation(n: SyntaxTerm, d: SyntaxTerm, rem: bool) -> SyntaxTerm {
    SyntaxTerm::Call {
        name: if rem {
            "truncating_remainder"
        } else {
            "truncating_quotient"
        }
        .into(),
        arguments: vec![n, d],
    }
}
fn apply(name: &str, args: Vec<SyntaxTerm>, mut premises: Vec<SyntaxProposition>) -> ProofStep {
    // Partial values used as theorem arguments retain their explicit domains.
    // These guards come from the written arguments, not an ambient fact scan.
    for argument in &args {
        super::super::fixed_state_proofs::conversion_conditions::walk_written_expressions(
            argument,
            &mut |expression| {
                if let SyntaxTerm::Call { name, arguments } = expression
                    && matches!(
                        name.as_str(),
                        "truncating_quotient" | "truncating_remainder"
                    )
                    && let [_, divisor] = arguments.as_slice()
                {
                    let guard = ne(divisor.clone(), lit(0));
                    if !premises.contains(&guard) {
                        premises.push(guard);
                    }
                }
            },
        );
    }
    ProofStep::ApplyPlannedTheorem {
        application: TheoremApplication {
            name: format!("click::integer::{name}"),
            arguments: args,
        },
        premises,
    }
}
fn have(p: SyntaxProposition, steps: Vec<ProofStep>) -> ProofStep {
    super::super::wide_arithmetic::have(p, steps)
}
fn known(steps: &mut Vec<ProofStep>, p: SyntaxProposition) {
    steps.push(have(p, vec![ProofStep::Known]));
}
fn proved(
    steps: &mut Vec<ProofStep>,
    p: SyntaxProposition,
    name: &str,
    args: Vec<SyntaxTerm>,
    ps: Vec<SyntaxProposition>,
) {
    steps.push(have(p, vec![apply(name, args, ps)]));
}
fn trans(steps: &mut Vec<ProofStep>, a: SyntaxTerm, b: SyntaxTerm, c: SyntaxTerm) {
    proved(
        steps,
        le(a.clone(), c.clone()),
        "le_transitive",
        vec![a.clone(), b.clone(), c.clone()],
        vec![le(a, b.clone()), le(b, c)],
    );
}
// Exact selected facts retain both their source proposition and operand name.
type Endpoint = (BigInt, SyntaxProposition, SyntaxTerm);

fn positive_interval(
    n: SyntaxTerm,
    d: SyntaxTerm,
    ends: &[Endpoint; 4],
    target: &BigInt,
    lower: bool,
    rem: bool,
) -> Option<Vec<ProofStep>> {
    let mut steps = Vec::new();
    let (lo_n, hi_n, lo_d, hi_d) = (&ends[0].0, &ends[1].0, &ends[2].0, &ends[3].0);
    let ps = |i: usize| ends[i].1.clone();
    let pos = le(lit(1), d.clone());
    let nz = ne(d.clone(), lit(0));
    known(&mut steps, le(lit(1), c(lo_d)));
    // Use the selected range to prove the domain; never borrow an ambient guard.
    proved(
        &mut steps,
        pos.clone(),
        "le_transitive",
        vec![lit(1), c(lo_d), d.clone()],
        vec![le(lit(1), c(lo_d)), ps(2)],
    );
    proved(
        &mut steps,
        nz.clone(),
        "nonzero_from_one",
        vec![d.clone()],
        vec![pos.clone()],
    );
    let t = c(target);
    let domain = vec![nz.clone(), pos.clone()];
    if !rem {
        let rounded = if lower {
            target <= &BigInt::zero()
        } else {
            target >= &BigInt::zero()
        };
        let i = if lower { 0 } else { 1 };
        let j = if rounded { 2 } else { 3 };
        let endpoint = &ends[j].0;
        let mut threshold = target * endpoint;
        if rounded {
            if lower {
                threshold -= endpoint - 1;
            } else {
                threshold += endpoint - 1;
            }
        }
        if if lower {
            threshold > *lo_n
        } else {
            *hi_n > threshold
        } {
            return None;
        }
        let e = c(endpoint);
        let product = mul(t.clone(), e.clone());
        let threshold_expr = if rounded {
            if lower {
                sub(product, sub(e.clone(), lit(1)))
            } else {
                add(product, sub(e.clone(), lit(1)))
            }
        } else {
            product
        };
        let numeric = if lower {
            le(threshold_expr, c(lo_n))
        } else {
            le(c(hi_n), threshold_expr)
        };
        known(&mut steps, numeric.clone());
        let sign = if (lower && rounded) || (!lower && !rounded) {
            le(t.clone(), lit(0))
        } else {
            le(lit(0), t.clone())
        };
        known(&mut steps, sign.clone());
        let name = match (lower, rounded) {
            (true, true) => "quotient_lower_interval_nonpositive",
            (true, false) => "quotient_lower_interval_positive",
            (false, true) => "quotient_upper_interval_nonnegative",
            (false, false) => "quotient_upper_interval_negative",
        };
        let mut cited = domain;
        cited.extend([sign, ps(j), ps(i), numeric]);
        steps.push(apply(name, vec![n, d, c(&ends[i].0), e, t], cited));
    } else {
        let min_d = lo_d;
        let small = lo_n.abs().max(hi_n.abs()) < *min_d;
        if small {
            if if lower { target > lo_n } else { hi_n > target } {
                return None;
            }
            let small_lo = le(sub(lit(1), c(min_d)), c(lo_n));
            let small_hi = le(c(hi_n), sub(c(min_d), lit(1)));
            known(&mut steps, small_lo.clone());
            known(&mut steps, small_hi.clone());
            let r = operation(n.clone(), d.clone(), true);
            let equality = eq(r.clone(), n.clone());
            let mut cited = domain;
            cited.extend([ps(2), ps(0), ps(1), small_lo, small_hi]);
            proved(
                &mut steps,
                equality.clone(),
                "small_remainder_interval",
                vec![n.clone(), d, c(lo_n), c(hi_n), c(min_d)],
                cited,
            );
            if lower {
                known(&mut steps, le(t.clone(), c(lo_n)));
                trans(&mut steps, t.clone(), c(lo_n), n.clone());
                steps.push(apply(
                    "le_substitute",
                    vec![t.clone(), n.clone(), t.clone(), r.clone()],
                    vec![le(t.clone(), n), eq(t.clone(), t), equality],
                ));
            } else {
                known(&mut steps, le(c(hi_n), t.clone()));
                trans(&mut steps, n.clone(), c(hi_n), t.clone());
                steps.push(apply(
                    "le_substitute",
                    vec![n.clone(), t.clone(), r, t.clone()],
                    vec![le(n, t.clone()), equality, eq(t.clone(), t)],
                ));
            }
        } else {
            let dividend = if lower {
                target <= lo_n && target <= &BigInt::zero()
            } else {
                hi_n <= target && &BigInt::zero() <= target
            };
            if dividend {
                let i = if lower { 0 } else { 1 };
                let numeric = if lower {
                    le(t.clone(), c(lo_n))
                } else {
                    le(c(hi_n), t.clone())
                };
                let sign = if lower {
                    le(t.clone(), lit(0))
                } else {
                    le(lit(0), t.clone())
                };
                known(&mut steps, numeric.clone());
                known(&mut steps, sign.clone());
                let mut cited = domain;
                cited.extend([ps(i), numeric, sign]);
                steps.push(apply(
                    if lower {
                        "remainder_lower_from_dividend"
                    } else {
                        "remainder_upper_from_dividend"
                    },
                    vec![n, d, c(&ends[i].0), t],
                    cited,
                ));
            } else {
                let endpoint: BigInt = hi_d - 1;
                if if lower {
                    target > &(-endpoint.clone())
                } else {
                    &endpoint > target
                } {
                    return None;
                }
                let numeric = if lower {
                    le(t.clone(), sub(lit(1), c(hi_d)))
                } else {
                    le(sub(c(hi_d), lit(1)), t.clone())
                };
                known(&mut steps, numeric.clone());
                let mut cited = domain;
                cited.extend([ps(3), numeric]);
                steps.push(apply(
                    if lower {
                        "remainder_lower_from_divisor"
                    } else {
                        "remainder_upper_from_divisor"
                    },
                    vec![n, d, c(hi_d), t],
                    cited,
                ));
            }
        }
    }
    Some(steps)
}

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    pub(in crate::surface::proof) fn try_division_bound_using(
        input: &Proof<'a>,
        premises: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_division_bound_using");
        fn has_division(p: &Proposition) -> bool {
            match p {
                Proposition::Not(p) => has_division(p),
                condition_source_0 @ Proposition::ConditionIs(_, _)
                    if let Some((
                        OldConditionTerm::IntegerLessEqual(a, b)
                        | OldConditionTerm::IntegerGreaterEqual(a, b)
                        | OldConditionTerm::IntegerLessThan(a, b)
                        | OldConditionTerm::IntegerGreaterThan(a, b),
                        _,
                    )) = condition_source_0.old_condition() =>
                {
                    [a, b].iter().any(|x| {
                        matches!(
                            x.as_ref(),
                            I::TruncatingQuotient(..) | I::TruncatingRemainder(..)
                        )
                    })
                }
                _ => false,
            }
        }
        if !input.goal().is_some_and(has_division) {
            return Ok(None);
        }
        let Some(surface) = input
            .surface_goal()
            .and_then(integer_composition::canonical_surface)
        else {
            return Ok(None);
        };
        let Some((written_left, ComparisonOperator::LessEqual, written_right)) =
            integer_surface_ordered_parts(&surface)
        else {
            return Ok(None);
        };
        let kernel = input.lower_integer_surface_proposition(&surface, "division bound")?;
        let Some((OldConditionTerm::IntegerLessEqual(left, right), true)) = kernel.old_condition()
        else {
            return Ok(None);
        };
        let get = |x: &SharedIntegerTerm| match x.as_ref() {
            I::TruncatingQuotient(n, d) => Some((n.clone(), d.clone(), false)),
            I::TruncatingRemainder(n, d) => Some((n.clone(), d.clone(), true)),
            _ => None,
        };
        let (n, d, rem, target, lower, written_target) = if let Some((n, d, r)) = get(left) {
            (n, d, r, right, false, written_right)
        } else if let Some((n, d, r)) = get(right) {
            (n, d, r, left, true, written_left)
        } else {
            return Ok(None);
        };
        let mut sources = Vec::new();
        for source in premises {
            let Some(written) = integer_composition::canonical_surface(source) else {
                continue;
            };
            let Some((wa, ComparisonOperator::LessEqual, wb)) =
                integer_surface_ordered_parts(&written)
            else {
                continue;
            };
            let p = input.lower_integer_surface_proposition(&written, "division premise")?;
            let readings = if matches!(&p, condition_source_0 @ Proposition::ConditionIs(_, _) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::Compare { .. }, _))))
            {
                crate::kernel::machine_integer::comparison::integer_readings_with_promotions(&p)
            } else {
                vec![p]
            };
            for p in readings {
                if let Some((OldConditionTerm::IntegerLessEqual(a, b), true)) = (p).old_condition()
                {
                    sources.push((source.clone(), wa.clone(), wb.clone(), a.clone(), b.clone()));
                }
            }
        }
        let mut steps = Vec::new();
        // The two-premise positive-divisor rule also supports symbolic bounds.
        if !rem {
            for (positive, _, wd, a, b) in &sources {
                if a.as_const().is_none_or(|v| !v.is_one()) || b != &d {
                    continue;
                }
                let product: SharedIntegerTerm =
                    I::multiply(target.as_ref().clone(), d.as_ref().clone()).into();
                for (scaled, wa, wb, x, y) in &sources {
                    if if lower {
                        x != &product || y != &n
                    } else {
                        x != &n || y != &product
                    } {
                        continue;
                    }
                    let wn = if lower { wb } else { wa };
                    let nz = ne(wd.clone(), lit(0));
                    proved(
                        &mut steps,
                        nz.clone(),
                        "nonzero_from_one",
                        vec![wd.clone()],
                        vec![positive.clone()],
                    );
                    steps.push(apply(
                        if lower {
                            "positive_divisor_quotient_lower"
                        } else {
                            "positive_divisor_quotient_upper"
                        },
                        vec![wn.clone(), wd.clone(), written_target.clone()],
                        vec![nz, positive.clone(), scaled.clone()],
                    ));
                    return Self::apply_division_steps(input, steps).map(Some);
                }
            }
        }
        let Some(target) = target.as_const() else {
            return Ok(None);
        };
        let mut selected: [Option<Endpoint>; 4] = std::array::from_fn(|_| None);
        for (source, wa, wb, a, b) in &sources {
            for (i, operand) in [&n, &d].iter().enumerate() {
                for (upper, bounded, endpoint, written) in [(false, b, a, wb), (true, a, b, wa)] {
                    if bounded.value_read() != operand.value_read() {
                        continue;
                    }
                    let Some(value) = endpoint.as_const() else {
                        continue;
                    };
                    let j = i * 2 + usize::from(upper);
                    if selected[j]
                        .as_ref()
                        .is_none_or(|(old, _, _)| if upper { value < old } else { value > old })
                    {
                        selected[j] = Some((value.clone(), source.clone(), written.clone()));
                    }
                }
            }
        }
        let [Some(e0), Some(e1), Some(e2), Some(e3)] = selected else {
            return Ok(None);
        };
        if e0.0 > e1.0 || e2.0 > e3.0 || (e2.0 <= BigInt::zero() && e3.0 >= BigInt::zero()) {
            return Ok(None);
        }
        // Charge exact threshold arithmetic before computing it.
        let bits = |n: &BigInt| {
            usize::try_from(n.bits())
                .unwrap_or(usize::MAX)
                .saturating_add(1)
        };
        let work = bits(target)
            .saturating_mul(bits(&e2.0).max(bits(&e3.0)))
            .saturating_add(bits(&e0.0) + bits(&e1.0));
        if crate::instrumentation::deadline_exceeded_with_work(work) {
            return Ok(None);
        }
        let wn = e0.2.clone();
        let wd = e2.2.clone();
        if e2.0 > BigInt::zero() {
            let ends = [e0, e1, e2, e3];
            let Some(p) = positive_interval(wn, wd, &ends, target, lower, rem) else {
                return Ok(None);
            };
            steps.extend(p);
        } else {
            let nd = neg(wd.clone());
            let nz = ne(wd.clone(), lit(0));
            known(&mut steps, le(c(&e3.0), lit(-1)));
            proved(
                &mut steps,
                le(wd.clone(), lit(-1)),
                "le_transitive",
                vec![wd.clone(), c(&e3.0), lit(-1)],
                vec![e3.1.clone(), le(c(&e3.0), lit(-1))],
            );
            proved(
                &mut steps,
                nz.clone(),
                "nonzero_from_negative_one",
                vec![wd.clone()],
                vec![le(wd.clone(), lit(-1))],
            );
            let mut transformed = Vec::new();
            for (e, lo) in [(&e3, true), (&e2, false)] {
                let v = -e.0.clone();
                let original = neg(c(&e.0));
                let value = c(&v);
                let raw = if lo {
                    le(original.clone(), nd.clone())
                } else {
                    le(nd.clone(), original.clone())
                };
                let args = if lo {
                    vec![wd.clone(), c(&e.0)]
                } else {
                    vec![c(&e.0), wd.clone()]
                };
                proved(
                    &mut steps,
                    raw.clone(),
                    "negate_order",
                    args,
                    vec![e.1.clone()],
                );
                let equality = eq(value.clone(), original.clone());
                known(&mut steps, equality.clone());
                let named = if lo {
                    le(value.clone(), nd.clone())
                } else {
                    le(nd.clone(), value.clone())
                };
                let args = if lo {
                    vec![original.clone(), nd.clone(), value.clone(), nd.clone()]
                } else {
                    vec![nd.clone(), original.clone(), nd.clone(), value.clone()]
                };
                proved(
                    &mut steps,
                    named.clone(),
                    "le_substitute",
                    args,
                    vec![raw, equality, eq(nd.clone(), nd.clone())],
                );
                transformed.push((v, named, nd.clone()));
            }
            let ends = [e0, e1, transformed.remove(0), transformed.remove(0)];
            known(&mut steps, le(lit(1), c(&ends[2].0)));
            proved(
                &mut steps,
                le(lit(1), nd.clone()),
                "le_transitive",
                vec![lit(1), c(&ends[2].0), nd.clone()],
                vec![le(lit(1), c(&ends[2].0)), ends[2].1.clone()],
            );
            let negative_nonzero = ne(nd.clone(), lit(0));
            proved(
                &mut steps,
                negative_nonzero.clone(),
                "nonzero_from_one",
                vec![nd.clone()],
                vec![le(lit(1), nd.clone())],
            );
            let transformed_target = if rem { target.clone() } else { -target };
            let transformed_lower = if rem { lower } else { !lower };
            let Some(p) = positive_interval(
                wn.clone(),
                nd.clone(),
                &ends,
                &transformed_target,
                transformed_lower,
                rem,
            ) else {
                return Ok(None);
            };
            let original = operation(wn.clone(), wd.clone(), rem);
            let changed = operation(wn.clone(), nd.clone(), rem);
            let t = c(target);
            let tt = c(&transformed_target);
            let positive_goal = if transformed_lower {
                le(tt.clone(), changed.clone())
            } else {
                le(changed.clone(), tt.clone())
            };
            steps.push(have(positive_goal.clone(), p));
            let equality = eq(
                original.clone(),
                if rem {
                    changed.clone()
                } else {
                    neg(changed.clone())
                },
            );
            proved(
                &mut steps,
                equality.clone(),
                if rem {
                    "remainder_negate_divisor"
                } else {
                    "quotient_negate_divisor"
                },
                vec![wn, wd],
                vec![nz, negative_nonzero],
            );
            if rem {
                let args = if lower {
                    vec![t.clone(), changed.clone(), t.clone(), original]
                } else {
                    vec![changed.clone(), t.clone(), original, t.clone()]
                };
                steps.push(apply(
                    "le_substitute",
                    args,
                    vec![positive_goal, equality, eq(t.clone(), t)],
                ));
            } else {
                let double = neg(tt.clone());
                let negq = neg(changed.clone());
                let reversed = if lower {
                    le(double.clone(), negq.clone())
                } else {
                    le(negq.clone(), double.clone())
                };
                let args = if transformed_lower {
                    vec![tt.clone(), changed]
                } else {
                    vec![changed, tt.clone()]
                };
                proved(
                    &mut steps,
                    reversed.clone(),
                    "negate_order",
                    args,
                    vec![positive_goal],
                );
                let double_eq = eq(t.clone(), double.clone());
                known(&mut steps, double_eq.clone());
                let args = if lower {
                    vec![double, negq, t, original]
                } else {
                    vec![negq, double, original, t]
                };
                steps.push(apply(
                    "le_substitute",
                    args,
                    vec![reversed, equality, double_eq],
                ));
            }
        }
        Self::apply_division_steps(input, steps).map(Some)
    }

    fn apply_division_steps(
        input: &Proof<'a>,
        steps: Vec<ProofStep>,
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("apply_division_steps");
        let mut proof = input.clone();
        for step in steps {
            proof = match step {
                ProofStep::Have {
                    proposition,
                    proof: body,
                } => Self::apply_division_have(&proof, proposition, body.into_steps())?,
                step => proof.driver().apply_step(step)?,
            };
        }
        if proof.focused_discharged() {
            Ok(proof)
        } else {
            proof.driver().apply_step(ProofStep::Known)
        }
    }

    // Applying a theorem can leave an equivalent goal open (for example
    // Negate(Constant(4)) versus the written literal -4). Record an explicit
    // known step exactly where congruence, rather than the application, closes it.
    fn apply_division_have(
        input: &Proof<'a>,
        proposition: SyntaxProposition,
        steps: Vec<ProofStep>,
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("apply_division_have");
        let mut scope = input.driver().open_have(proposition)?;
        for step in steps {
            scope = match step {
                ProofStep::Have { proposition, proof } => {
                    let next =
                        Self::apply_division_have(scope.body(), proposition, proof.into_steps())?;
                    scope.join_nested_result(next)?
                }
                step => scope.driver().apply_step(step)?,
            };
        }
        if !scope.body().focused_discharged() {
            scope = scope.driver().apply_step(ProofStep::Known)?;
        }
        scope.join()
    }
}
