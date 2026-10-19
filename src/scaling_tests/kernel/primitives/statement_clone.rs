use super::*;
use crate::kernel::CExpression;

#[test]
fn statement_clone_uses_a_work_stack_for_nested_branches() {
    for depth in [4, 16, 64, 256] {
        std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(move || {
                let mut statement = CStatement::Return(CExpression::Value(crate::kernel::int32(1)));
                for index in 0..depth {
                    statement = CStatement::If {
                        condition: CExpression::Variable(format!("a{index}")),
                        then_branch: Box::new(statement),
                        else_branch: Box::new(CStatement::Skip),
                    };
                }
                let (copy, work) =
                    crate::instrumentation::measure_deterministic_work(|| statement.clone());
                assert_eq!(work, 2 * depth + 1, "depth {depth}");
                let mut left = &statement;
                let mut right = &copy;
                for index in (0..depth).rev() {
                    let CStatement::If {
                        condition,
                        then_branch,
                        else_branch,
                    } = left
                    else {
                        panic!("original branch {index}")
                    };
                    let CStatement::If {
                        condition: copied_condition,
                        then_branch: copied_then,
                        else_branch: copied_else,
                    } = right
                    else {
                        panic!("copied branch {index}")
                    };
                    assert_eq!(condition, copied_condition);
                    assert_eq!(else_branch.as_ref(), &CStatement::Skip);
                    assert_eq!(copied_else.as_ref(), &CStatement::Skip);
                    left = then_branch;
                    right = copied_then;
                }
                assert_eq!(left, right);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
