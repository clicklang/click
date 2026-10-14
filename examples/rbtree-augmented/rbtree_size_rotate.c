/* SPDX-License-Identifier: GPL-2.0-or-later
 * Unchanged RB_DECLARE_CALLBACKS rotate body specialized for sized_node.
 */
#include "rbtree_size.h"
int32 compute_size(struct sized_node *node, int32 exit);
static void sized_rotate(struct rb_node *rb_old, struct rb_node *rb_new)
{
    struct sized_node *old = rb_entry(rb_old, struct sized_node, rb);
    struct sized_node *new = rb_entry(rb_new, struct sized_node, rb);
    new->size = old->size;
    compute_size(old, false);
}
