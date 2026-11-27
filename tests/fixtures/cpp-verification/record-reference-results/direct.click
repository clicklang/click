import click::separation;
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
    step(); step();
    have call(0).result == &outer.child by { close(); }
    // The two adjacent views occupy one range ending before the written field.
    have 0 <= 2 by { close(); }
    have 2 <= 3 by { close(); }
    have separate(memory((&outer as (int32 *))[0..2]), memory((&outer as (int32 *))[2..3])) by {
        apply(click::separation::separate_adjacent_ranges(&outer as (int32 *), 0, 2, 3));
    }
    have separate(memory((&outer as (int32 *))[2..3]), memory((&outer as (int32 *))[0..2])) by {
        apply(click::separation::separate_symm(memory((&outer as (int32 *))[0..2]), memory((&outer as (int32 *))[2..3])));
    }
    step() by {
        rewrite(call(0).result, &outer.child);
        close();
    }

    have separate(region(2).footprint, memory((&outer.first)[0..1]));
    have separate(region(2).footprint, memory((&outer.child.sibling)[0..1]));
    have outer.first == at(region(2).entry, outer.first) by {
        preserve(memory((&outer.first)[0..1]), region(2));
    }
    have outer.child.sibling == at(region(2).entry, outer.child.sibling) by {
        preserve(memory((&outer.child.sibling)[0..1]), region(2));
    }
    step_until(function.exit);
    have result == outer.child.value;
    have region(0).result == old(outer.first);
    close();
}
