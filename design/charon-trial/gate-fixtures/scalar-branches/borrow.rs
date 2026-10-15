pub fn branch_update(parent: &mut i32, choose: bool) {
    let child = &mut *parent;
    if choose {
        *child = 7;
    } else {
        *child = 9;
    }
    *parent += 1;
}

pub fn nested_branch_update(parent: &mut i32, choose: bool) {
    let child = &mut *parent;
    let grandchild = &mut *child;
    if choose {
        *grandchild = 7;
    } else {
        *grandchild = 9;
    }
    *child += 1;
    *parent += 1;
}

pub fn branch_caller(parent: &mut i32, choose: bool) {
    branch_update(parent, choose);
}
