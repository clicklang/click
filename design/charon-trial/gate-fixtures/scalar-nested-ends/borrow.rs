pub fn shared_frontier(parent: &mut i32) {
    let child = &mut *parent;
    let grandchild = &mut *child;
    *grandchild = 7;
    *parent = 8;
}

pub fn separate_frontiers(parent: &mut i32) {
    let child = &mut *parent;
    {
        let grandchild = &mut *child;
        *grandchild = 7;
    }
    *child += 1;
    *parent += 1;
}

pub fn nested_caller(parent: &mut i32) {
    shared_frontier(parent);
}
