verifying "rbtree_size_rotate.c";
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_compute.click";

void sized_rotate(struct rb_node* rb_old, struct rb_node* rb_new) {
    requires rb_old != 0;
    requires rb_new != 0;
    requires rb_old != rb_new;
    views (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left;
    views (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right;
    owns source: size_metadata(rb_old);
    owns target: size_metadata(rb_new);
    owns left: optional_size((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left);
    owns right: optional_size((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right);
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != 0 or left.value == 0;
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != rb_old;
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size));
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size));
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != 0 or right.value == 0;
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != rb_old;
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size));
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size));
    requires separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory((rb_new as (uint8 *) as (struct sized_node *))->size));
    requires separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory((rb_new as (uint8 *) as (struct sized_node *))->size));
    requires 0 <= left.value;
    requires 0 <= right.value;
    requires right.value <= 2147483646;
    requires left.value <= 2147483646 - right.value;
    ensures target.value == old(source.value);
    ensures source.value == 1 + old(left.value) + old(right.value);
    ensures left.value == old(left.value);
    ensures right.value == old(right.value);
    ensures rb_old->rb_left == old(rb_old->rb_left);
    ensures rb_old->rb_right == old(rb_old->rb_right);
} by {
    unfold(source);
    unfold(target);
    // Evaluate both container_of conversions before opening the child caches.
    step_until(statement(2).entry);
    apply(size_sum_defined(left.value, right.value));
    // Prove each live child is distinct using its separately owned cache.
    // Then carry both link reads across the cache copy, call and return.
    if (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != 0 {
        if (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != 0 {
            have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                cases {
                    (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 => { close(); }
                    separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                }
            }
            have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                cases {
                    (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 => { close(); }
                    separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                }
            }
            have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                cases {
                    (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 => { close(); }
                    separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                }
            }
            have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                cases {
                    (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 => { close(); }
                    separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                }
            }
            unfold(left);
            have separate(memory(((old->rb.rb_left as (uint8 *)) as (struct sized_node *))->size), memory(((rb_old as (uint8 *)) as (struct sized_node *))->size)) by close();
            have load<int32>(old(&(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *)) as (struct sized_node *))->size)) == old(left.value) by close();
            fold(left) by { close() using { load<int32>(old(&(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *)) as (struct sized_node *))->size)) == old(left.value); }; }
            have &((old->rb.rb_left as (uint8 *)) as (struct sized_node *))->size != &((rb_old as (uint8 *)) as (struct sized_node *))->size by {
                close() using { separate(memory(((old->rb.rb_left as (uint8 *)) as (struct sized_node *))->size), memory(((rb_old as (uint8 *)) as (struct sized_node *))->size)); };
            }
            have old->rb.rb_left != ((old as (uint8 *)) as (struct rb_node *)) by {
                if old->rb.rb_left == ((old as (uint8 *)) as (struct rb_node *)) {
                    have &((old->rb.rb_left as (uint8 *)) as (struct sized_node *))->size == &((rb_old as (uint8 *)) as (struct sized_node *))->size by { rewrite(old->rb.rb_left, ((old as (uint8 *)) as (struct rb_node *))); close(); }
                    close();
                } else {
                    close();
                }
            }
            unfold(right);
            have separate(memory(((old->rb.rb_right as (uint8 *)) as (struct sized_node *))->size), memory(((rb_old as (uint8 *)) as (struct sized_node *))->size)) by close();
            have load<int32>(old(&(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *)) as (struct sized_node *))->size)) == old(right.value) by close();
            fold(right) by { close() using { load<int32>(old(&(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *)) as (struct sized_node *))->size)) == old(right.value); }; }
            have &((old->rb.rb_right as (uint8 *)) as (struct sized_node *))->size != &((rb_old as (uint8 *)) as (struct sized_node *))->size by {
                close() using { separate(memory(((old->rb.rb_right as (uint8 *)) as (struct sized_node *))->size), memory(((rb_old as (uint8 *)) as (struct sized_node *))->size)); };
            }
            have old->rb.rb_right != ((old as (uint8 *)) as (struct rb_node *)) by {
                if old->rb.rb_right == ((old as (uint8 *)) as (struct rb_node *)) {
                    have &((old->rb.rb_right as (uint8 *)) as (struct sized_node *))->size == &((rb_old as (uint8 *)) as (struct sized_node *))->size by { rewrite(old->rb.rb_right, ((old as (uint8 *)) as (struct rb_node *))); close(); }
                    close();
                } else {
                    close();
                }
            }
            have old->size == old(source.value);
            have separate(memory(old->size), memory(new->size));

            have separate(memory(old->rb.rb_left), memory(new->size));
            have separate(memory(old->rb.rb_right), memory(new->size));
            have separate(memory(new->size), memory((old as (int32 *))[2..6])) by { apply(separate_size_write_from_child_links(old as (int32 *), memory(new->size))); }
            have separate(memory((&new->size)[0..1]), memory((old as (int32 *))[2..6])) by {
                apply(click::separation::contains_refl(memory(new->size)));
                apply(click::separation::contains_refl(memory((old as (int32 *))[2..6])));
                apply(click::separation::separate_restrict(memory(new->size), memory((old as (int32 *))[2..6]), memory((&new->size)[0..1]), memory((old as (int32 *))[2..6])));
            }
            have defined(old->rb.rb_right) by close();
            have defined(old->rb.rb_left) by close();
            mark before_copy;
            step() by { close() using { separate(memory((&new->size)[0..1]), memory((old as (int32 *))[2..6])); }; }
            // The layout ranges include padding, while the copy accesses one int32 cell.
            have contains(memory(new->size), memory((&new->size)[0..1])) by apply(click::separation::contains_refl(memory(new->size)));
            have contains(memory(old->size), memory((&old->size)[0..1])) by apply(click::separation::contains_refl(memory(old->size)));
            have separate(memory((&old->size)[0..1]), memory((&new->size)[0..1])) by {
                apply(click::separation::separate_restrict(memory(old->size), memory(new->size), memory((&old->size)[0..1]), memory((&new->size)[0..1])));
            }
            have separate(statement(2).footprint, memory((&old->size)[0..1])) by {
                close() using { separate(memory((&old->size)[0..1]), memory((&new->size)[0..1])); };
            }
            have old->size == at(before_copy, old->size) by {
                preserve(memory((&old->size)[0..1]), statement(2));
            }
            have old->size == old(source.value) by {
                rewrite(old->size, at(before_copy, old->size)); close();
            }
            have contains(memory(old->rb.rb_left), memory(old->rb.rb_left)) by {
                apply(click::separation::contains_refl(memory(old->rb.rb_left)));
            }
            have separate(memory(old->rb.rb_left), memory((&new->size)[0..1])) by {
                apply(click::separation::separate_restrict(memory(old->rb.rb_left), memory(new->size), memory(old->rb.rb_left), memory((&new->size)[0..1])));
            }
            have separate(statement(2).footprint, memory(old->rb.rb_left)) by {
                close() using { separate(memory(old->rb.rb_left), memory((&new->size)[0..1])); };
            }
            have defined(old->rb.rb_left) by { preserve(memory(old->rb.rb_left), statement(2)); }
            have old->rb.rb_left == at(before_copy, old->rb.rb_left) by {
                preserve(memory(old->rb.rb_left), statement(2));
            }

            have contains(memory(old->rb.rb_right), memory(old->rb.rb_right)) by {
                apply(click::separation::contains_refl(memory(old->rb.rb_right)));
            }
            have separate(memory(old->rb.rb_right), memory((&new->size)[0..1])) by {
                apply(click::separation::separate_restrict(memory(old->rb.rb_right), memory(new->size), memory(old->rb.rb_right), memory((&new->size)[0..1])));
            }
            have separate(statement(2).footprint, memory(old->rb.rb_right)) by {
                close() using { separate(memory(old->rb.rb_right), memory((&new->size)[0..1])); };
            }
            have defined(old->rb.rb_right) by { preserve(memory(old->rb.rb_right), statement(2)); }
            have old->rb.rb_right == at(before_copy, old->rb.rb_right) by {
                preserve(memory(old->rb.rb_right), statement(2));
            }

            let target = fold(size_metadata(rb_new), { value: old(source.value) });
            fold(source);
            apply(click::separation::separate_adjacent_ranges(old as (int32 *), 2, 6, 8));
            apply(click::separation::separate_symm(memory((old as (int32 *))[2..6]), memory((old as (int32 *))[6..8])));
            apply(separate_size_write_from_child_links(old as (int32 *), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (int32 *))[6..8])));
            apply(separate_size_write_from_child_links(old as (int32 *), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (int32 *))[6..8])));
            have separate(source, memory((old as (int32 *))[2..6])) by close();
            have separate(left, memory((old as (int32 *))[2..6])) by close();
            have separate(right, memory((old as (int32 *))[2..6])) by close();
            mark before_compute;
            step(compute_size, { parent: source, left: left, right: right });
            have contains(at(before_compute, source) * at(before_compute, left) * at(before_compute, right), statement(3).call(compute_size, 0).footprint) by close();
            apply(click::separation::separate_star(at(before_compute, source), at(before_compute, left), memory((old as (int32 *))[2..6])));
            apply(click::separation::separate_star(at(before_compute, source) * at(before_compute, left), at(before_compute, right), memory((old as (int32 *))[2..6])));
            apply(click::separation::contains_subrange(old as (int32 *), 2, 6, 2, 4));
            have separate(statement(3).call(compute_size, 0).footprint, memory(old->rb.rb_right)) by {
                apply(click::separation::separate_restrict(at(before_compute, source) * at(before_compute, left) * at(before_compute, right), memory((old as (int32 *))[2..6]), statement(3).call(compute_size, 0).footprint, memory(old->rb.rb_right)));
            }
            have defined(old->rb.rb_right) by { preserve(memory(old->rb.rb_right), statement(3).call(compute_size, 0)); }
            have old->rb.rb_right == at(before_compute, old->rb.rb_right) by { preserve(memory(old->rb.rb_right), statement(3).call(compute_size, 0)); }
            apply(click::separation::contains_subrange(old as (int32 *), 2, 6, 4, 6));
            have separate(statement(3).call(compute_size, 0).footprint, memory(old->rb.rb_left)) by {
                apply(click::separation::separate_restrict(at(before_compute, source) * at(before_compute, left) * at(before_compute, right), memory((old as (int32 *))[2..6]), statement(3).call(compute_size, 0).footprint, memory(old->rb.rb_left)));
            }
            have defined(old->rb.rb_left) by { preserve(memory(old->rb.rb_left), statement(3).call(compute_size, 0)); }
            have old->rb.rb_left == at(before_compute, old->rb.rb_left) by { preserve(memory(old->rb.rb_left), statement(3).call(compute_size, 0)); }
            step();
            have separate(region(14).footprint, memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right)) by close();
            have defined((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right) by { preserve(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), region(14)); }
            have separate(region(14).footprint, memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left)) by close();
            have defined((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left) by { preserve(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), region(14)); }
            close();
        } else {
            have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                cases {
                    (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 => { close(); }
                    separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                }
            }
            have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                cases {
                    (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 => { close(); }
                    separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                }
            }
            unfold(left);
            have separate(memory(((old->rb.rb_left as (uint8 *)) as (struct sized_node *))->size), memory(((rb_old as (uint8 *)) as (struct sized_node *))->size)) by close();
            have load<int32>(old(&(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *)) as (struct sized_node *))->size)) == old(left.value) by close();
            fold(left) by { close() using { load<int32>(old(&(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *)) as (struct sized_node *))->size)) == old(left.value); }; }
            have &((old->rb.rb_left as (uint8 *)) as (struct sized_node *))->size != &((rb_old as (uint8 *)) as (struct sized_node *))->size by {
                close() using { separate(memory(((old->rb.rb_left as (uint8 *)) as (struct sized_node *))->size), memory(((rb_old as (uint8 *)) as (struct sized_node *))->size)); };
            }
            have old->rb.rb_left != ((old as (uint8 *)) as (struct rb_node *)) by {
                if old->rb.rb_left == ((old as (uint8 *)) as (struct rb_node *)) {
                    have &((old->rb.rb_left as (uint8 *)) as (struct sized_node *))->size == &((rb_old as (uint8 *)) as (struct sized_node *))->size by { rewrite(old->rb.rb_left, ((old as (uint8 *)) as (struct rb_node *))); close(); }
                    close();
                } else {
                    close();
                }
            }
            have old->rb.rb_right != ((old as (uint8 *)) as (struct rb_node *)) by close();
            have old->size == old(source.value);
            have separate(memory(old->size), memory(new->size));

            have separate(memory(old->rb.rb_left), memory(new->size));
            have separate(memory(old->rb.rb_right), memory(new->size));
            have separate(memory(new->size), memory((old as (int32 *))[2..6])) by { apply(separate_size_write_from_child_links(old as (int32 *), memory(new->size))); }
            have separate(memory((&new->size)[0..1]), memory((old as (int32 *))[2..6])) by {
                apply(click::separation::contains_refl(memory(new->size)));
                apply(click::separation::contains_refl(memory((old as (int32 *))[2..6])));
                apply(click::separation::separate_restrict(memory(new->size), memory((old as (int32 *))[2..6]), memory((&new->size)[0..1]), memory((old as (int32 *))[2..6])));
            }
            have defined(old->rb.rb_right) by close();
            have defined(old->rb.rb_left) by close();
            mark before_copy;
            step() by { close() using { separate(memory((&new->size)[0..1]), memory((old as (int32 *))[2..6])); }; }
            // The layout ranges include padding, while the copy accesses one int32 cell.
            have contains(memory(new->size), memory((&new->size)[0..1])) by apply(click::separation::contains_refl(memory(new->size)));
            have contains(memory(old->size), memory((&old->size)[0..1])) by apply(click::separation::contains_refl(memory(old->size)));
            have separate(memory((&old->size)[0..1]), memory((&new->size)[0..1])) by {
                apply(click::separation::separate_restrict(memory(old->size), memory(new->size), memory((&old->size)[0..1]), memory((&new->size)[0..1])));
            }
            have separate(statement(2).footprint, memory((&old->size)[0..1])) by {
                close() using { separate(memory((&old->size)[0..1]), memory((&new->size)[0..1])); };
            }
            have old->size == at(before_copy, old->size) by {
                preserve(memory((&old->size)[0..1]), statement(2));
            }
            have old->size == old(source.value) by {
                rewrite(old->size, at(before_copy, old->size)); close();
            }
            have contains(memory(old->rb.rb_left), memory(old->rb.rb_left)) by {
                apply(click::separation::contains_refl(memory(old->rb.rb_left)));
            }
            have separate(memory(old->rb.rb_left), memory((&new->size)[0..1])) by {
                apply(click::separation::separate_restrict(memory(old->rb.rb_left), memory(new->size), memory(old->rb.rb_left), memory((&new->size)[0..1])));
            }
            have separate(statement(2).footprint, memory(old->rb.rb_left)) by {
                close() using { separate(memory(old->rb.rb_left), memory((&new->size)[0..1])); };
            }
            have defined(old->rb.rb_left) by { preserve(memory(old->rb.rb_left), statement(2)); }
            have old->rb.rb_left == at(before_copy, old->rb.rb_left) by {
                preserve(memory(old->rb.rb_left), statement(2));
            }

            have contains(memory(old->rb.rb_right), memory(old->rb.rb_right)) by {
                apply(click::separation::contains_refl(memory(old->rb.rb_right)));
            }
            have separate(memory(old->rb.rb_right), memory((&new->size)[0..1])) by {
                apply(click::separation::separate_restrict(memory(old->rb.rb_right), memory(new->size), memory(old->rb.rb_right), memory((&new->size)[0..1])));
            }
            have separate(statement(2).footprint, memory(old->rb.rb_right)) by {
                close() using { separate(memory(old->rb.rb_right), memory((&new->size)[0..1])); };
            }
            have defined(old->rb.rb_right) by { preserve(memory(old->rb.rb_right), statement(2)); }
            have old->rb.rb_right == at(before_copy, old->rb.rb_right) by {
                preserve(memory(old->rb.rb_right), statement(2));
            }

            let target = fold(size_metadata(rb_new), { value: old(source.value) });
            fold(source);
            apply(click::separation::separate_adjacent_ranges(old as (int32 *), 2, 6, 8));
            apply(click::separation::separate_symm(memory((old as (int32 *))[2..6]), memory((old as (int32 *))[6..8])));
            apply(separate_size_write_from_child_links(old as (int32 *), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (int32 *))[6..8])));
            have separate(source, memory((old as (int32 *))[2..6])) by close();
            have separate(left, memory((old as (int32 *))[2..6])) by close();
            have separate(right, memory((old as (int32 *))[2..6])) by close();
            mark before_compute;
            step(compute_size, { parent: source, left: left, right: right });
            have contains(at(before_compute, source) * at(before_compute, left) * at(before_compute, right), statement(3).call(compute_size, 0).footprint) by close();
            apply(click::separation::separate_star(at(before_compute, source), at(before_compute, left), memory((old as (int32 *))[2..6])));
            apply(click::separation::separate_star(at(before_compute, source) * at(before_compute, left), at(before_compute, right), memory((old as (int32 *))[2..6])));
            apply(click::separation::contains_subrange(old as (int32 *), 2, 6, 2, 4));
            have separate(statement(3).call(compute_size, 0).footprint, memory(old->rb.rb_right)) by {
                apply(click::separation::separate_restrict(at(before_compute, source) * at(before_compute, left) * at(before_compute, right), memory((old as (int32 *))[2..6]), statement(3).call(compute_size, 0).footprint, memory(old->rb.rb_right)));
            }
            have defined(old->rb.rb_right) by { preserve(memory(old->rb.rb_right), statement(3).call(compute_size, 0)); }
            have old->rb.rb_right == at(before_compute, old->rb.rb_right) by { preserve(memory(old->rb.rb_right), statement(3).call(compute_size, 0)); }
            apply(click::separation::contains_subrange(old as (int32 *), 2, 6, 4, 6));
            have separate(statement(3).call(compute_size, 0).footprint, memory(old->rb.rb_left)) by {
                apply(click::separation::separate_restrict(at(before_compute, source) * at(before_compute, left) * at(before_compute, right), memory((old as (int32 *))[2..6]), statement(3).call(compute_size, 0).footprint, memory(old->rb.rb_left)));
            }
            have defined(old->rb.rb_left) by { preserve(memory(old->rb.rb_left), statement(3).call(compute_size, 0)); }
            have old->rb.rb_left == at(before_compute, old->rb.rb_left) by { preserve(memory(old->rb.rb_left), statement(3).call(compute_size, 0)); }
            step();
            have separate(region(14).footprint, memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right)) by close();
            have defined((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right) by { preserve(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), region(14)); }
            have separate(region(14).footprint, memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left)) by close();
            have defined((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left) by { preserve(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), region(14)); }
            close();
        }
    } else {
        if (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != 0 {
            have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                cases {
                    (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 => { close(); }
                    separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                }
            }
            have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                cases {
                    (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 => { close(); }
                    separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                }
            }
            have old->rb.rb_left != ((old as (uint8 *)) as (struct rb_node *)) by close();
            unfold(right);
            have separate(memory(((old->rb.rb_right as (uint8 *)) as (struct sized_node *))->size), memory(((rb_old as (uint8 *)) as (struct sized_node *))->size)) by close();
            have load<int32>(old(&(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *)) as (struct sized_node *))->size)) == old(right.value) by close();
            fold(right) by { close() using { load<int32>(old(&(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *)) as (struct sized_node *))->size)) == old(right.value); }; }
            have &((old->rb.rb_right as (uint8 *)) as (struct sized_node *))->size != &((rb_old as (uint8 *)) as (struct sized_node *))->size by {
                close() using { separate(memory(((old->rb.rb_right as (uint8 *)) as (struct sized_node *))->size), memory(((rb_old as (uint8 *)) as (struct sized_node *))->size)); };
            }
            have old->rb.rb_right != ((old as (uint8 *)) as (struct rb_node *)) by {
                if old->rb.rb_right == ((old as (uint8 *)) as (struct rb_node *)) {
                    have &((old->rb.rb_right as (uint8 *)) as (struct sized_node *))->size == &((rb_old as (uint8 *)) as (struct sized_node *))->size by { rewrite(old->rb.rb_right, ((old as (uint8 *)) as (struct rb_node *))); close(); }
                    close();
                } else {
                    close();
                }
            }
            have old->size == old(source.value);
            have separate(memory(old->size), memory(new->size));

            have separate(memory(old->rb.rb_left), memory(new->size));
            have separate(memory(old->rb.rb_right), memory(new->size));
            have separate(memory(new->size), memory((old as (int32 *))[2..6])) by { apply(separate_size_write_from_child_links(old as (int32 *), memory(new->size))); }
            have separate(memory((&new->size)[0..1]), memory((old as (int32 *))[2..6])) by {
                apply(click::separation::contains_refl(memory(new->size)));
                apply(click::separation::contains_refl(memory((old as (int32 *))[2..6])));
                apply(click::separation::separate_restrict(memory(new->size), memory((old as (int32 *))[2..6]), memory((&new->size)[0..1]), memory((old as (int32 *))[2..6])));
            }
            have defined(old->rb.rb_right) by close();
            have defined(old->rb.rb_left) by close();
            mark before_copy;
            step() by { close() using { separate(memory((&new->size)[0..1]), memory((old as (int32 *))[2..6])); }; }
            // The layout ranges include padding, while the copy accesses one int32 cell.
            have contains(memory(new->size), memory((&new->size)[0..1])) by apply(click::separation::contains_refl(memory(new->size)));
            have contains(memory(old->size), memory((&old->size)[0..1])) by apply(click::separation::contains_refl(memory(old->size)));
            have separate(memory((&old->size)[0..1]), memory((&new->size)[0..1])) by {
                apply(click::separation::separate_restrict(memory(old->size), memory(new->size), memory((&old->size)[0..1]), memory((&new->size)[0..1])));
            }
            have separate(statement(2).footprint, memory((&old->size)[0..1])) by {
                close() using { separate(memory((&old->size)[0..1]), memory((&new->size)[0..1])); };
            }
            have old->size == at(before_copy, old->size) by {
                preserve(memory((&old->size)[0..1]), statement(2));
            }
            have old->size == old(source.value) by {
                rewrite(old->size, at(before_copy, old->size)); close();
            }
            have contains(memory(old->rb.rb_left), memory(old->rb.rb_left)) by {
                apply(click::separation::contains_refl(memory(old->rb.rb_left)));
            }
            have separate(memory(old->rb.rb_left), memory((&new->size)[0..1])) by {
                apply(click::separation::separate_restrict(memory(old->rb.rb_left), memory(new->size), memory(old->rb.rb_left), memory((&new->size)[0..1])));
            }
            have separate(statement(2).footprint, memory(old->rb.rb_left)) by {
                close() using { separate(memory(old->rb.rb_left), memory((&new->size)[0..1])); };
            }
            have defined(old->rb.rb_left) by { preserve(memory(old->rb.rb_left), statement(2)); }
            have old->rb.rb_left == at(before_copy, old->rb.rb_left) by {
                preserve(memory(old->rb.rb_left), statement(2));
            }

            have contains(memory(old->rb.rb_right), memory(old->rb.rb_right)) by {
                apply(click::separation::contains_refl(memory(old->rb.rb_right)));
            }
            have separate(memory(old->rb.rb_right), memory((&new->size)[0..1])) by {
                apply(click::separation::separate_restrict(memory(old->rb.rb_right), memory(new->size), memory(old->rb.rb_right), memory((&new->size)[0..1])));
            }
            have separate(statement(2).footprint, memory(old->rb.rb_right)) by {
                close() using { separate(memory(old->rb.rb_right), memory((&new->size)[0..1])); };
            }
            have defined(old->rb.rb_right) by { preserve(memory(old->rb.rb_right), statement(2)); }
            have old->rb.rb_right == at(before_copy, old->rb.rb_right) by {
                preserve(memory(old->rb.rb_right), statement(2));
            }

            let target = fold(size_metadata(rb_new), { value: old(source.value) });
            fold(source);
            apply(click::separation::separate_adjacent_ranges(old as (int32 *), 2, 6, 8));
            apply(click::separation::separate_symm(memory((old as (int32 *))[2..6]), memory((old as (int32 *))[6..8])));
            apply(separate_size_write_from_child_links(old as (int32 *), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (int32 *))[6..8])));
            have separate(source, memory((old as (int32 *))[2..6])) by close();
            have separate(left, memory((old as (int32 *))[2..6])) by close();
            have separate(right, memory((old as (int32 *))[2..6])) by close();
            mark before_compute;
            step(compute_size, { parent: source, left: left, right: right });
            have contains(at(before_compute, source) * at(before_compute, left) * at(before_compute, right), statement(3).call(compute_size, 0).footprint) by close();
            apply(click::separation::separate_star(at(before_compute, source), at(before_compute, left), memory((old as (int32 *))[2..6])));
            apply(click::separation::separate_star(at(before_compute, source) * at(before_compute, left), at(before_compute, right), memory((old as (int32 *))[2..6])));
            apply(click::separation::contains_subrange(old as (int32 *), 2, 6, 2, 4));
            have separate(statement(3).call(compute_size, 0).footprint, memory(old->rb.rb_right)) by {
                apply(click::separation::separate_restrict(at(before_compute, source) * at(before_compute, left) * at(before_compute, right), memory((old as (int32 *))[2..6]), statement(3).call(compute_size, 0).footprint, memory(old->rb.rb_right)));
            }
            have defined(old->rb.rb_right) by { preserve(memory(old->rb.rb_right), statement(3).call(compute_size, 0)); }
            have old->rb.rb_right == at(before_compute, old->rb.rb_right) by { preserve(memory(old->rb.rb_right), statement(3).call(compute_size, 0)); }
            apply(click::separation::contains_subrange(old as (int32 *), 2, 6, 4, 6));
            have separate(statement(3).call(compute_size, 0).footprint, memory(old->rb.rb_left)) by {
                apply(click::separation::separate_restrict(at(before_compute, source) * at(before_compute, left) * at(before_compute, right), memory((old as (int32 *))[2..6]), statement(3).call(compute_size, 0).footprint, memory(old->rb.rb_left)));
            }
            have defined(old->rb.rb_left) by { preserve(memory(old->rb.rb_left), statement(3).call(compute_size, 0)); }
            have old->rb.rb_left == at(before_compute, old->rb.rb_left) by { preserve(memory(old->rb.rb_left), statement(3).call(compute_size, 0)); }
            step();
            have separate(region(14).footprint, memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right)) by close();
            have defined((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right) by { preserve(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), region(14)); }
            have separate(region(14).footprint, memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left)) by close();
            have defined((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left) by { preserve(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), region(14)); }
            close();
        } else {
            have old->rb.rb_left != ((old as (uint8 *)) as (struct rb_node *)) by close();
            have old->rb.rb_right != ((old as (uint8 *)) as (struct rb_node *)) by close();
            have old->size == old(source.value);
            have separate(memory(old->size), memory(new->size));

            have separate(memory(old->rb.rb_left), memory(new->size));
            have separate(memory(old->rb.rb_right), memory(new->size));
            have separate(memory(new->size), memory((old as (int32 *))[2..6])) by { apply(separate_size_write_from_child_links(old as (int32 *), memory(new->size))); }
            have separate(memory((&new->size)[0..1]), memory((old as (int32 *))[2..6])) by {
                apply(click::separation::contains_refl(memory(new->size)));
                apply(click::separation::contains_refl(memory((old as (int32 *))[2..6])));
                apply(click::separation::separate_restrict(memory(new->size), memory((old as (int32 *))[2..6]), memory((&new->size)[0..1]), memory((old as (int32 *))[2..6])));
            }
            have defined(old->rb.rb_right) by close();
            have defined(old->rb.rb_left) by close();
            mark before_copy;
            step() by { close() using { separate(memory((&new->size)[0..1]), memory((old as (int32 *))[2..6])); }; }
            // The layout ranges include padding, while the copy accesses one int32 cell.
            have contains(memory(new->size), memory((&new->size)[0..1])) by apply(click::separation::contains_refl(memory(new->size)));
            have contains(memory(old->size), memory((&old->size)[0..1])) by apply(click::separation::contains_refl(memory(old->size)));
            have separate(memory((&old->size)[0..1]), memory((&new->size)[0..1])) by {
                apply(click::separation::separate_restrict(memory(old->size), memory(new->size), memory((&old->size)[0..1]), memory((&new->size)[0..1])));
            }
            have separate(statement(2).footprint, memory((&old->size)[0..1])) by {
                close() using { separate(memory((&old->size)[0..1]), memory((&new->size)[0..1])); };
            }
            have old->size == at(before_copy, old->size) by {
                preserve(memory((&old->size)[0..1]), statement(2));
            }
            have old->size == old(source.value) by {
                rewrite(old->size, at(before_copy, old->size)); close();
            }
            have contains(memory(old->rb.rb_left), memory(old->rb.rb_left)) by {
                apply(click::separation::contains_refl(memory(old->rb.rb_left)));
            }
            have separate(memory(old->rb.rb_left), memory((&new->size)[0..1])) by {
                apply(click::separation::separate_restrict(memory(old->rb.rb_left), memory(new->size), memory(old->rb.rb_left), memory((&new->size)[0..1])));
            }
            have separate(statement(2).footprint, memory(old->rb.rb_left)) by {
                close() using { separate(memory(old->rb.rb_left), memory((&new->size)[0..1])); };
            }
            have defined(old->rb.rb_left) by { preserve(memory(old->rb.rb_left), statement(2)); }
            have old->rb.rb_left == at(before_copy, old->rb.rb_left) by {
                preserve(memory(old->rb.rb_left), statement(2));
            }

            have contains(memory(old->rb.rb_right), memory(old->rb.rb_right)) by {
                apply(click::separation::contains_refl(memory(old->rb.rb_right)));
            }
            have separate(memory(old->rb.rb_right), memory((&new->size)[0..1])) by {
                apply(click::separation::separate_restrict(memory(old->rb.rb_right), memory(new->size), memory(old->rb.rb_right), memory((&new->size)[0..1])));
            }
            have separate(statement(2).footprint, memory(old->rb.rb_right)) by {
                close() using { separate(memory(old->rb.rb_right), memory((&new->size)[0..1])); };
            }
            have defined(old->rb.rb_right) by { preserve(memory(old->rb.rb_right), statement(2)); }
            have old->rb.rb_right == at(before_copy, old->rb.rb_right) by {
                preserve(memory(old->rb.rb_right), statement(2));
            }

            let target = fold(size_metadata(rb_new), { value: old(source.value) });
            fold(source);
            apply(click::separation::separate_adjacent_ranges(old as (int32 *), 2, 6, 8));
            apply(click::separation::separate_symm(memory((old as (int32 *))[2..6]), memory((old as (int32 *))[6..8])));
            have separate(source, memory((old as (int32 *))[2..6])) by close();
            have separate(left, memory((old as (int32 *))[2..6])) by close();
            have separate(right, memory((old as (int32 *))[2..6])) by close();
            mark before_compute;
            step(compute_size, { parent: source, left: left, right: right });
            have contains(at(before_compute, source) * at(before_compute, left) * at(before_compute, right), statement(3).call(compute_size, 0).footprint) by close();
            apply(click::separation::separate_star(at(before_compute, source), at(before_compute, left), memory((old as (int32 *))[2..6])));
            apply(click::separation::separate_star(at(before_compute, source) * at(before_compute, left), at(before_compute, right), memory((old as (int32 *))[2..6])));
            apply(click::separation::contains_subrange(old as (int32 *), 2, 6, 2, 4));
            have separate(statement(3).call(compute_size, 0).footprint, memory(old->rb.rb_right)) by {
                apply(click::separation::separate_restrict(at(before_compute, source) * at(before_compute, left) * at(before_compute, right), memory((old as (int32 *))[2..6]), statement(3).call(compute_size, 0).footprint, memory(old->rb.rb_right)));
            }
            have defined(old->rb.rb_right) by { preserve(memory(old->rb.rb_right), statement(3).call(compute_size, 0)); }
            have old->rb.rb_right == at(before_compute, old->rb.rb_right) by { preserve(memory(old->rb.rb_right), statement(3).call(compute_size, 0)); }
            apply(click::separation::contains_subrange(old as (int32 *), 2, 6, 4, 6));
            have separate(statement(3).call(compute_size, 0).footprint, memory(old->rb.rb_left)) by {
                apply(click::separation::separate_restrict(at(before_compute, source) * at(before_compute, left) * at(before_compute, right), memory((old as (int32 *))[2..6]), statement(3).call(compute_size, 0).footprint, memory(old->rb.rb_left)));
            }
            have defined(old->rb.rb_left) by { preserve(memory(old->rb.rb_left), statement(3).call(compute_size, 0)); }
            have old->rb.rb_left == at(before_compute, old->rb.rb_left) by { preserve(memory(old->rb.rb_left), statement(3).call(compute_size, 0)); }
            step();
            have separate(region(14).footprint, memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right)) by close();
            have defined((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right) by { preserve(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), region(14)); }
            have separate(region(14).footprint, memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left)) by close();
            have defined((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left) by { preserve(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), region(14)); }
            close();
        }
    }
}

contract void RotateSize(struct rb_node* rb_old, struct rb_node* rb_new) {
    requires rb_old != 0;
    requires rb_new != 0;
    requires rb_old != rb_new;
    views (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left;
    views (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right;
    owns source: size_metadata(rb_old);
    owns target: size_metadata(rb_new);
    owns left: optional_size((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left);
    owns right: optional_size((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right);
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != 0 or left.value == 0;
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != rb_old;
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size));
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size));
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != 0 or right.value == 0;
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != rb_old;
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size));
    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size));
    requires separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory((rb_new as (uint8 *) as (struct sized_node *))->size));
    requires separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory((rb_new as (uint8 *) as (struct sized_node *))->size));
    requires 0 <= left.value;
    requires 0 <= right.value;
    requires right.value <= 2147483646;
    requires left.value <= 2147483646 - right.value;
    ensures target.value == old(source.value);
    ensures source.value == 1 + old(left.value) + old(right.value);
    ensures left.value == old(left.value);
    ensures right.value == old(right.value);
}

theorem sized_rotate_has_size_contract()
    executes sized_rotate(struct rb_node* rb_old, struct rb_node* rb_new) {
    ensures RotateSize(&sized_rotate) as { source: s, target: t, left: l, right: r } by {
        have rb_old != 0 by close();
        have rb_new != 0 by close();
        have rb_old != rb_new by close();
        apply(size_sum_defined(l.value, r.value));
        apply(click::separation::separate_adjacent_ranges(rb_old as (int32 *), 2, 6, 8));
        apply(click::separation::separate_symm(
            memory((rb_old as (int32 *))[2..6]), memory((rb_old as (int32 *))[6..8])));
        apply(separate_size_write_from_child_links(rb_old as (int32 *),
            memory((rb_new as (int32 *))[6..8])));
        if (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != 0 {
            if (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != 0 {
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 => { close(); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                    }
                }
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 => { close(); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                    }
                }
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 => { close(); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                    }
                }
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 => { close(); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                    }
                }
                apply(separate_size_write_from_child_links(rb_old as (int32 *), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (int32 *))[6..8])));
                apply(separate_size_write_from_child_links(rb_old as (int32 *), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (int32 *))[6..8])));
                step(sized_rotate, { source: s, target: t, left: l, right: r }) {
                    requires rb_old != 0 by close();
                    requires rb_new != 0 by close();
                    requires rb_old != rb_new by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != 0 or l.value == 0 by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != rb_old by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != 0 or r.value == 0 by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != rb_old by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory((rb_new as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory((rb_new as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires 0 <= l.value by close();
                    requires 0 <= r.value by close();
                    requires r.value <= 2147483646 by close();
                    requires l.value <= 2147483646 - r.value by close();
                }
                close();
            } else {
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 => { close(); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                    }
                }
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 => { close(); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                    }
                }
                apply(separate_size_write_from_child_links(rb_old as (int32 *), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (int32 *))[6..8])));
                step(sized_rotate, { source: s, target: t, left: l, right: r }) {
                    requires rb_old != 0 by close();
                    requires rb_new != 0 by close();
                    requires rb_old != rb_new by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != 0 or l.value == 0 by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != rb_old by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != 0 or r.value == 0 by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != rb_old by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory((rb_new as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory((rb_new as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires 0 <= l.value by close();
                    requires 0 <= r.value by close();
                    requires r.value <= 2147483646 by close();
                    requires l.value <= 2147483646 - r.value by close();
                }
                close();
            }
        } else {
            if (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != 0 {
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 => { close(); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                    }
                }
                have separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 => { close(); }
                        separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { close(); }
                    }
                }
                apply(separate_size_write_from_child_links(rb_old as (int32 *), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (int32 *))[6..8])));
                step(sized_rotate, { source: s, target: t, left: l, right: r }) {
                    requires rb_old != 0 by close();
                    requires rb_new != 0 by close();
                    requires rb_old != rb_new by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != 0 or l.value == 0 by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != rb_old by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != 0 or r.value == 0 by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != rb_old by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory((rb_new as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory((rb_new as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires 0 <= l.value by close();
                    requires 0 <= r.value by close();
                    requires r.value <= 2147483646 by close();
                    requires l.value <= 2147483646 - r.value by close();
                }
                close();
            } else {
                step(sized_rotate, { source: s, target: t, left: l, right: r }) {
                    requires rb_old != 0 by close();
                    requires rb_new != 0 by close();
                    requires rb_old != rb_new by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != 0 or l.value == 0 by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left != rb_old by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != 0 or r.value == 0 by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right != rb_old by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 or separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory(((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), memory((rb_new as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires separate(memory((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), memory((rb_new as (uint8 *) as (struct sized_node *))->size)) by close();
                    requires 0 <= l.value by close();
                    requires 0 <= r.value by close();
                    requires r.value <= 2147483646 by close();
                    requires l.value <= 2147483646 - r.value by close();
                }
                close();
            }
        }
    }
}
