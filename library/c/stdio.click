// A successful write (nonnegative result) accepts the whole message into
// stdout. An error leaves the amount written unspecified. The stream may
// buffer output before delivering it to its destination.
spec enum StdoutWrite {
    Attempt(List<uint8>, int32),
}

abstract resource stdout() {
    // Newest attempted write first.
    field writes: List<StdoutWrite>;
    field last_result: int32;
}
