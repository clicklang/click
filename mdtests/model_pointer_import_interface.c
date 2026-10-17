struct model_node { unsigned long long word; };
void imported_node(struct model_node* p) {}
void typed_caller(struct model_node* p) { imported_node(p); }
void untyped_caller(void* p) { imported_node((struct model_node*)p); }
