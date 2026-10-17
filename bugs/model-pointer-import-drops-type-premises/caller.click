import "library.click";
verifying "case.c";
void caller(void* p) { produces held: token(); ensures true; } by {
    let { held: held } = step(wrapped((struct model_node*)p), {}); execute();
}
