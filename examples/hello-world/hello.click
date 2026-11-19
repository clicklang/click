verifying "hello.c";
import click::c::stdio::{stream, write_requests};

int32 main() {
    owns out: stream(stdout);
    ensures write_requests(out.write_history)
        == List::Cons(b"hello, world\n", List::Nil);
} by {
    unfold(write_requests(List<WriteAttempt>::Nil));
}
