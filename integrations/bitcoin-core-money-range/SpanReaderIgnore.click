verifying "span-probe.cpp";

void SpanReader::ignore(uint64 n) throws std::ios_base::failure {
    owns this->m_data;
    views std_span_data(this->m_data)[0..std_span_size(this->m_data)];
    ensures n <= old(std_span_size(this->m_data));
    ensures std_span_data(this->m_data) == old(std_span_data(this->m_data)) + n;
    ensures std_span_size(this->m_data) == old(std_span_size(this->m_data)) - n;
    ensures forall (k: uint64) { k < old(std_span_size(this->m_data)) implies old(std_span_data(this->m_data))[k] == old(std_span_data(this->m_data)[k]) };
    exceptional ensures old(std_span_size(this->m_data)) < n;
    exceptional ensures std_span_data(this->m_data) == old(std_span_data(this->m_data));
    exceptional ensures std_span_size(this->m_data) == old(std_span_size(this->m_data));
    exceptional ensures forall (k: uint64) { k < old(std_span_size(this->m_data)) implies old(std_span_data(this->m_data))[k] == old(std_span_data(this->m_data)[k]) };
}

void probe(struct SpanReader& reader, uint64 n) throws std::ios_base::failure {
    owns reader.m_data;
    views std_span_data(reader.m_data)[0..std_span_size(reader.m_data)];
    ensures n <= old(std_span_size(reader.m_data));
    ensures std_span_data(reader.m_data) == old(std_span_data(reader.m_data)) + n;
    ensures std_span_size(reader.m_data) == old(std_span_size(reader.m_data)) - n;
    ensures forall (k: uint64) { k < old(std_span_size(reader.m_data)) implies old(std_span_data(reader.m_data))[k] == old(std_span_data(reader.m_data)[k]) };
    exceptional ensures old(std_span_size(reader.m_data)) < n;
    exceptional ensures std_span_data(reader.m_data) == old(std_span_data(reader.m_data));
    exceptional ensures std_span_size(reader.m_data) == old(std_span_size(reader.m_data));
    exceptional ensures forall (k: uint64) { k < old(std_span_size(reader.m_data)) implies old(std_span_data(reader.m_data))[k] == old(std_span_data(reader.m_data)[k]) };
}
