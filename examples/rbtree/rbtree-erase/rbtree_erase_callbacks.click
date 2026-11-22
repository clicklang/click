verifying "rb_erase.c";
import "../rbtree-model/rbtree_resources.click";

contract void AugmentRotate(struct rb_node* old, struct rb_node* new) {
    requires new != 0; ensures 1 == 1;
}
contract void ErasePropagate(struct rb_node* node, struct rb_node* stop) {
    ensures 1 == 1;
}

contract void EraseCopy(struct rb_node* node, struct rb_node* successor) {
    requires node != 0;
    requires successor != 0;
    ensures 1 == 1;
}

resource erase_callbacks(augment: const struct rb_augment_callbacks*) {
    views *augment;
    fact ErasePropagate(augment->propagate);
    fact EraseCopy(augment->copy);
    fact AugmentRotate(augment->rotate);
}

void dummy_propagate(struct rb_node* node, struct rb_node* stop) {
    ensures 1 == 1;
} by { step_until(function.exit); known(); }
void dummy_copy(struct rb_node* old, struct rb_node* new) {
    requires old != 0;
    requires new != 0;
    ensures 1 == 1;
} by { step_until(function.exit); solve(); }
void dummy_rotate(struct rb_node* old, struct rb_node* new) {
    requires new != 0;
    ensures 1 == 1;
} by { step_until(function.exit); known(); }

theorem dummy_propagate_contract() {
    ensures ErasePropagate(&dummy_propagate) by { unfold(ErasePropagate(&dummy_propagate)); solve(); }
}
theorem dummy_copy_contract() {
    ensures EraseCopy(&dummy_copy) by { unfold(EraseCopy(&dummy_copy)); solve(); }
}
theorem dummy_rotate_contract() {
    ensures AugmentRotate(&dummy_rotate) by { unfold(AugmentRotate(&dummy_rotate)); solve(); }
}


// Shared by the unlink and color-repair proofs.
void rb_set_parent(struct rb_node* rb, struct rb_node* p) {
    owns rb->__rb_parent_color;
    ensures rb->__rb_parent_color == ((old(rb->__rb_parent_color) & 1) | address(p));
    ensures aligned(p, 8) implies ((rb->__rb_parent_color & ~3) as (struct rb_node *)) == p;
} by {
    if aligned(p, 8) { step_until(function.exit); }
    else { step_until(function.exit); }
}
