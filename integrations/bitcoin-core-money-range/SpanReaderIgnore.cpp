// Fixture harness; SpanReader::ignore is the unchanged pinned Bitcoin source.
#include <streams.h>
void probe(SpanReader& reader, size_t n) { reader.ignore(n); }
