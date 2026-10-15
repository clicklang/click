// Scaling tests of `src/languages/rust/lowering/moves/flow.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn split_while_headers_preserve_order_and_have_linear_work_and_emitted_size() {
    for width in [8, 32, 128] {
        let mut blocks = (0..width)
            .map(|index| {
                let mut b = block(if index + 1 == width {
                    branch(width, width + 1)
                } else {
                    T::Goto { target: index + 1 }
                });
                b.statements.push(S::Assign {
                    target: E::Local {
                        name: "marker".into(),
                    },
                    value: E::Integer {
                        value: index as i32,
                    },
                });
                b
            })
            .collect::<Vec<_>>();
        let mut body = block(T::Goto { target: 0 });
        body.statements.push(S::Assign {
            target: E::Local {
                name: "marker".into(),
            },
            value: E::Integer { value: -1 },
        });
        blocks.push(body);
        blocks.push(block(T::Return));
        let f = function(blocks);
        let flow = Flow::analyze(&f, f.mir.as_ref().unwrap()).unwrap();
        assert_eq!(flow.loops[&0].headers, (0..width).collect::<Vec<_>>());
        assert_eq!(flow.loops[&0].test, width - 1);
        let export = RustExport {
            schema: 8,
            compiler_commit: String::new(),
            target: String::new(),
            edition: "2024".into(),
            overflow_checks: true,
            panic: "abort".into(),
            mir_opt_level: 0,
            logical_source: "flow.rs".into(),
            records: vec![],
            functions: vec![f],
        };
        let (lowered, work) = crate::instrumentation::measure_deterministic_work(|| {
            super::super::super::super::lower(&export)
        });
        let function = lowered.unwrap().0[0].to_kernel_function();
        let mut pending = vec![function.body()];
        let (mut loops, mut assignments, mut nodes) = (0, 0, 0);
        while let Some(statement) = pending.pop() {
            nodes += 1;
            match statement {
                CStatement::Seq(a, b) => pending.extend([a.as_ref(), b.as_ref()]),
                CStatement::While { body, .. } => {
                    loops += 1;
                    pending.push(body);
                }
                CStatement::Assign { name, .. } if name == "marker" => assignments += 1,
                CStatement::Break => panic!("do not manufacture a break"),
                _ => (),
            }
        }
        assert_eq!(loops, 1);
        assert_eq!(assignments, width * 2 + 1);
        assert!(nodes < 32 * width, "width {width}: {nodes}");
        assert!(work < 128 * width, "width {width}: {work}");
    }
}

#[test]
fn nested_while_regions_have_linear_analysis_work_and_emitted_size() {
    for depth in [8, 32, 128] {
        let mut blocks = (0..depth)
            .map(|header| block(branch(header + 1, 2 * depth - header)))
            .collect::<Vec<_>>();
        blocks.push(block(T::Goto { target: depth - 1 }));
        for offset in 1..depth {
            blocks.push(block(T::Goto {
                target: depth - 1 - offset,
            }));
        }
        blocks.push(block(T::Return));
        for b in blocks.iter_mut().take(2 * depth) {
            b.statements.push(S::Assign {
                target: E::Local {
                    name: "marker".into(),
                },
                value: E::Integer { value: 0 },
            });
        }
        let f = function(blocks);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            Flow::analyze(&f, f.mir.as_ref().unwrap())
        });
        let flow = result.unwrap();
        assert_eq!(flow.order.len(), 2 * depth + 1);
        assert_eq!(flow.loops.len(), depth);
        assert!(work < 64 * depth, "depth {depth}: {work}");
        let export = RustExport {
            schema: 8,
            compiler_commit: String::new(),
            target: String::new(),
            edition: "2024".into(),
            overflow_checks: true,
            panic: "abort".into(),
            mir_opt_level: 0,
            logical_source: "flow.rs".into(),
            records: vec![],
            functions: vec![f],
        };
        let (functions, _) = super::super::super::super::lower(&export).unwrap();
        let kernel = functions[0].to_kernel_function();
        let mut pending = vec![kernel.body()];
        let (mut count, mut assignments) = (0, 0);
        while let Some(s) = pending.pop() {
            match s {
                CStatement::Seq(a, b) => pending.extend([a.as_ref(), b.as_ref()]),
                CStatement::While { body, .. } => {
                    count += 1;
                    pending.push(body);
                }
                CStatement::Assign { name, .. } if name == "marker" => assignments += 1,
                _ => (),
            }
        }
        assert_eq!(count, depth);
        assert_eq!(assignments, 3 * depth);
    }
}
