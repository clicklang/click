// C11 7.21.6.1: `fprintf` writes the characters its format produces to the
// stream. Click models a format of ordinary characters and `%%`; its
// variable arguments, which such a format does not convert, are evaluated
// and ignored. Each attempt adds the requested characters and the result to
// the front of the history: the count on success, or a negative value on an
// error, which may follow partial output.
int32 fprintf(FILE* file, const uint8* format, ...args) {
    let n: uint64;
    views click::c::string::cstr_at(format, n);
    requires n <= 2147483647u64;
    requires click::c::stdio::literal_format(format, 0u64, n as int32);
    owns out: click::c::stdio::stream(file);
    ensures result == click::c::stdio::format_length(format, 0u64, n as int32, 0) or result < 0;
    ensures out.write_history == List::Cons(
        WriteAttempt::Attempt(click::c::stdio::format_output(format, 0u64, n as int32), result),
        old(out.write_history));
    ensures click::c::stdio::write_requests(out.write_history) == List::Cons(
        click::c::stdio::format_output(format, 0u64, n as int32),
        old(click::c::stdio::write_requests(out.write_history)));
}
