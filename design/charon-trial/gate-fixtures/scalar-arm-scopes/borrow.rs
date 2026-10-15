pub fn scoped_update(parent: &mut i32, choose: bool) {
    if choose {
        let child = &mut *parent;
        let alias = child;
        *alias = 7;
    } else {
        let child = &mut *parent;
        *child = 9;
    }
    *parent += 1;
}

pub fn nested_scopes(parent: &mut i32, choose: bool, inner: bool) {
    if choose {
        let child = &mut *parent;
        if inner {
            let grandchild = &mut *child;
            *grandchild = 7;
        } else {
            let grandchild = &mut *child;
            *grandchild = 9;
        }
        *child += 1;
    } else {
        let child = &mut *parent;
        *child = 11;
    }
    *parent += 1;
}

pub fn scoped_caller(parent: &mut i32, choose: bool) {
    scoped_update(parent, choose);
}
