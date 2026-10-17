verifying "case.c";
spec enum NodeRef { At(struct model_node*), }
resource token() { field model: NodeRef; }
void wrapped(struct model_node* p) { produces held: token(); ensures true; } by {
    execute(); let held = fold(token(), { model: NodeRef::At(p) });
}

void caller(void* p) { produces held: token(); ensures true; } by {
    let { held: held } = step(wrapped((struct model_node*)p), {}); execute();
}
