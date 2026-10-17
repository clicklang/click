struct node { unsigned long long word; };
struct node* get(struct node* p) { return p; }
int caller(struct node* p) {
    struct node* q = get(p);
    if (q != 0) return 1;
    return 0;
}
