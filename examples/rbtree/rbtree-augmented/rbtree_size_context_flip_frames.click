// Owned frames shared by the two context color-flip proofs.
import "rbtree_size_context_resources.click";

// The recoloring calls change parent words, retaining every tree link.
resource sized_context_flip_links(root: struct rb_root*, x: struct rb_node*, y: struct rb_node*, z: struct rb_node*) {
    field top: int32*;
    field xl: int32*; field xr: int32*;
    field yl: int32*; field yr: int32*;
    field zl: int32*; field zr: int32*;
    owns root->rb_node;
    owns x->rb_left; owns x->rb_right;
    owns y->rb_left; owns y->rb_right;
    owns z->rb_left; owns z->rb_right;
    fact root->rb_node == top;
    fact x->rb_left == xl; fact x->rb_right == xr;
    fact y->rb_left == yl; fact y->rb_right == yr;
    fact z->rb_left == zl; fact z->rb_right == zr;
    fact xl != x; fact xr != x;
    fact yl != y; fact yr != y;
    fact zl != z; fact zr != z;
}
resource sized_context_flip_parent_word(p: struct rb_node*) {
    field up: int32*;
    field word: uint64;
    owns p->__rb_parent_color;
    fact p->__rb_parent_color == word;
    fact ((p->__rb_parent_color & ~3) as (struct rb_node*)) == up;
    fact (p->__rb_parent_color & 1) == color_bit(Color::Black);
}

// Each new black parent word is retained across the other recolorings.
resource sized_context_flip_black_word(p: struct rb_node*, up: struct rb_node*) {
    field word: uint64;
    owns p->__rb_parent_color;
    fact p->__rb_parent_color == word;
    fact ((p->__rb_parent_color & ~3) as (struct rb_node*)) == up;
    fact p->__rb_parent_color == address(up) + (p->__rb_parent_color & 1);
    fact (p->__rb_parent_color & 1) == color_bit(Color::Black);
}
