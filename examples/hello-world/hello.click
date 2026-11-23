verifying "hello.c";
import click::c::stdio::{stream, write_requests, format_output};

int32 main() {
    owns out: stream(stdout);
    ensures write_requests(out.write_history)
        == List::Cons(b"hello, world\n", List::Nil);
} by {
    step();
    have out.write_history == List::Cons(
        WriteAttempt::Attempt(format_output(main.string_literal(0), 0u64, 13), statement(0).result),
        List<WriteAttempt>::Nil) by known();
    unfold(write_requests(List<WriteAttempt>::Nil));
    unfold(write_requests(List::Cons(
        WriteAttempt::Attempt(format_output(main.string_literal(0), 0u64, 13), statement(0).result),
        List<WriteAttempt>::Nil)));
    have format_output(main.string_literal(0), 0u64, 13) == b"hello, world\n" by solve();
    have write_requests(out.write_history) == List::Cons(b"hello, world\n", List::Nil) by {
        rewrite(out.write_history, List::Cons(
            WriteAttempt::Attempt(format_output(main.string_literal(0), 0u64, 13), statement(0).result),
            List<WriteAttempt>::Nil));
        rewrite(write_requests(List::Cons(
            WriteAttempt::Attempt(format_output(main.string_literal(0), 0u64, 13), statement(0).result),
            List<WriteAttempt>::Nil)), List::Cons(format_output(main.string_literal(0), 0u64, 13), write_requests(List<WriteAttempt>::Nil)));
        rewrite(format_output(main.string_literal(0), 0u64, 13), b"hello, world\n");
        rewrite(write_requests(List<WriteAttempt>::Nil), List<List<uint8>>::Nil);
        known();
    }
}
