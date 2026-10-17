struct model_node { unsigned long long word; };
void wrapped(struct model_node* p) {}
void caller(void* p) { wrapped((struct model_node*)p); }
