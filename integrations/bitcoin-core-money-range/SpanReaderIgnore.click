import click::separation;
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
} by {
    have separate(memory((this as (uint8 *))[0..8]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))])) by { solve(); }
    have separate(memory((this as (uint8 *))[8..16]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))])) by { solve(); }
    have separate(memory((this as (uint8 *))[0..8]) * memory((this as (uint8 *))[8..16]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))])) by {
        apply(click::separation::separate_star(memory((this as (uint8 *))[0..8]), memory((this as (uint8 *))[8..16]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))]))) using {
            separate(memory((this as (uint8 *))[0..8]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))]));
            separate(memory((this as (uint8 *))[8..16]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))]));
        };
    }
    have contains(memory((this as (uint8 *))[0..8]) * memory((this as (uint8 *))[8..16]), memory((this as (uint8 *))[0..16])) by {
        apply(click::separation::contains_joined_ranges(this as (uint8 *), 0, 8, 16)) using {
            0 <= 8;
            8 <= 16;
        };
    }
    have contains(memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))])) by { apply(click::separation::contains_refl(memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))]))); }
    have separate(memory((this as (uint8 *))[0..16]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))])) by {
        apply(click::separation::separate_restrict(memory((this as (uint8 *))[0..8]) * memory((this as (uint8 *))[8..16]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))]), memory((this as (uint8 *))[0..16]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))]))) using {
            separate(memory((this as (uint8 *))[0..8]) * memory((this as (uint8 *))[8..16]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))]));
            contains(memory((this as (uint8 *))[0..8]) * memory((this as (uint8 *))[8..16]), memory((this as (uint8 *))[0..16]));
            contains(memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))]));
        };
    }

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
