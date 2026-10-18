verifying "model_pointer_import_interface.c";
spec enum ImportedNodeRef { At(struct model_node*), }
resource imported_node_token() { field model: ImportedNodeRef; }
void imported_node(struct model_node* p) {
    produces held: imported_node_token();
    ensures held.model == ImportedNodeRef::At(p);
} by {
    execute();
    let held = fold(imported_node_token(), { model: ImportedNodeRef::At(p) });
}
