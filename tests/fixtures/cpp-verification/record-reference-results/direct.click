verifying "direct.cpp";

Widget& Outer::get() {
    views this->child.value;
    ensures &result == &this->child;
}

const Widget& Outer::peek() const {
    views this->child.value;
    ensures &result == &this->child;
}

int32 probe(Outer& outer) {
    owns outer.child.value;
    views outer.first;
    views outer.child.sibling;
    ensures result == old(outer.first);
    ensures outer.child.value == result;
    ensures outer.first == old(outer.first);
    ensures outer.child.sibling == old(outer.child.sibling);
} by {
    step();
    let { result: child } = step();
    have child == &outer.child by { known(); }
    // The two adjacent views occupy one range ending before the written field.
    have separate(memory((&outer as (int32 *))[2..3]), memory((&outer as (int32 *))[0..2])) by {
        normalize() using {};
    }
    have separate(memory((child as (int32 *))[1]), memory((&outer as (int32 *))[0..2])) by {
        rewrite(child, &outer.child);
        known();
    }
    step();
}
