/* SPDX-License-Identifier: GPL-2.0-or-later
 * Unchanged RB_DECLARE_CALLBACKS propagate body specialized for sized_node.
 */
#include "rbtree_size.h"

int32 compute_size(struct sized_node *node, int32 exit);

static inline void
sized_propagate(struct rb_node *rb, struct rb_node *stop)
{
    while (rb != stop) {
        struct sized_node *node = rb_entry(rb, struct sized_node, rb);
        if (compute_size(node, true))
            break;
        rb = rb_parent(&node->rb);
    }
}
