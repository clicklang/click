verifying "hello.c";
import click::c::stdio;

function greeting() -> List<uint8> {
    List::Cons('h', List::Cons('e', List::Cons('l', List::Cons('l',
    List::Cons('o', List::Cons(',', List::Cons(' ', List::Cons('w',
    List::Cons('o', List::Cons('r', List::Cons('l', List::Cons('d',
    List::Cons('\n', List::Nil)))))))))))))
}

int32 main() {
    owns out: stdio::stdout();
    ensures out.writes == List::Cons(
        StdoutWrite::Attempt(greeting(), out.last_result), List::Nil);
    ensures out.last_result == 13 or out.last_result < 0;
}
