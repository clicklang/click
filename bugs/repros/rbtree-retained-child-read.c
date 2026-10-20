struct node { unsigned long word; struct node *right; struct node *left; };
void set_word(struct node *m, struct node *p) { m->word = (unsigned long)p | 1; }
void probe(struct node *g, struct node *n) {
    while (1) {
        struct node *p = g->left;
        struct node *tmp = n->left;
        p->right = tmp;
        n->left = p;
        set_word(tmp, p);
        n = p;
        break;
    }
}
