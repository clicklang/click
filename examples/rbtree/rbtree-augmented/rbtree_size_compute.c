/* SPDX-License-Identifier: GPL-2.0-or-later
 * Concrete subtree-size recomputation client using Linux rb_entry.
 */
#include "rbtree_size.h"

int32 compute_size(struct sized_node *node, int32 exit)
{
    int32 size = 1;
    if (node->rb.rb_left) {
        struct sized_node *left = rb_entry(node->rb.rb_left, struct sized_node, rb);
        size += left->size;
    }
    if (node->rb.rb_right) {
        struct sized_node *right = rb_entry(node->rb.rb_right, struct sized_node, rb);
        size += right->size;
    }
    if (exit && node->size == size)
        return 1;
    node->size = size;
    return 0;
}
