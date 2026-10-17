verifying "case.c";
spec enum NodeRef { At(struct model_node*), }
resource token() { field model: NodeRef; }
void wrapped(struct model_node* p) { produces held: token(); ensures true; } by {
    execute(); let held = fold(token(), { model: NodeRef::At(p) });
}
