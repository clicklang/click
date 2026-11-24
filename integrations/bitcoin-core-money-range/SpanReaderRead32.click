import click::integer;
import "SpanReaderRead.click";
verifying "span-probe.cpp";

uint32 le32toh_internal(uint32 little_endian_32bits) {
    ensures result == little_endian_32bits;
}

uint32 ser_readdata32<SpanReader>(struct SpanReader& s) throws std::ios_base::failure {
    owns s.m_data;
    views std_span_data(s.m_data)[0..std_span_size(s.m_data)];
    ensures 4u64 <= old(std_span_size(s.m_data));
    ensures std_span_data(s.m_data) == old(std_span_data(s.m_data)) + 4u64;
    ensures std_span_size(s.m_data) == old(std_span_size(s.m_data)) - 4u64;
    ensures result == old(
        (load<uint8>(std_span_data(s.m_data) + 0u64) as uint32)
        | ((load<uint8>(std_span_data(s.m_data) + 1u64) as uint32) << 8u32)
        | ((load<uint8>(std_span_data(s.m_data) + 2u64) as uint32) << 16u32)
        | ((load<uint8>(std_span_data(s.m_data) + 3u64) as uint32) << 24u32)
    );
    exceptional ensures old(std_span_size(s.m_data)) < 4u64;
    exceptional ensures std_span_data(s.m_data) == old(std_span_data(s.m_data));
    exceptional ensures std_span_size(s.m_data) == old(std_span_size(s.m_data));
} by {
    // The writable byte span is backed by the local word.
    step_until(call(1).entry);
    step();
    have std_span_size(call(1).result) == 4u64 by { close(); }
    have std_span_data(call(1).result) == ((&obj) as (uint8 *)) by { close(); }
    step_until(call(2).entry);
    have separate(memory(((&obj) as (uint8 *))[0u64..4u64]), memory(old(std_span_data(s.m_data))[0u64..old(std_span_size(s.m_data))])) by { close(); }
    have separate(memory(at(call(1).exit, std_span_data(call(1).result))[0u64..std_span_size(call(1).result)]), memory(old(std_span_data(s.m_data))[0u64..old(std_span_size(s.m_data))])) by { close(); }
    outcomes {
        returned => {
            // Apply the reader's exact byte guarantees to the copied span parameter.
            have at(call(2).entry, std_span_size(call(2).parameter(dst))) == 4u64 by { close(); }
            have at(call(2).entry, std_span_data(call(2).parameter(dst))) == ((&obj) as (uint8 *)) by { close(); }
            have forall (k: uint64) { 0u64 <= k and k < at(call(2).entry, std_span_size(call(2).parameter(dst))) implies load<uint8>((at(call(2).entry, std_span_data(call(2).parameter(dst))) + k)) == at(call(2).entry, load<uint8>((std_span_data(s.m_data) + k))) and defined(load<uint8>((at(call(2).entry, std_span_data(call(2).parameter(dst))) + k))) } by { close(); }
            have 0u64 < at(call(2).entry, std_span_size(call(2).parameter(dst))) by { close(); }
            have defined(load<uint8>((std_span_data(call(2).parameter(dst)) + 0u64))) by { instantiate(forall (k: uint64) { 0u64 <= k and k < at(call(2).entry, std_span_size(call(2).parameter(dst))) implies load<uint8>((at(call(2).entry, std_span_data(call(2).parameter(dst))) + k)) == at(call(2).entry, load<uint8>((std_span_data(s.m_data) + k))) and defined(load<uint8>((at(call(2).entry, std_span_data(call(2).parameter(dst))) + k))) }, 0u64); close(); }
            have 1u64 < at(call(2).entry, std_span_size(call(2).parameter(dst))) by { close(); }
            have defined(load<uint8>((std_span_data(call(2).parameter(dst)) + 1u64))) by { instantiate(forall (k: uint64) { 0u64 <= k and k < at(call(2).entry, std_span_size(call(2).parameter(dst))) implies load<uint8>((at(call(2).entry, std_span_data(call(2).parameter(dst))) + k)) == at(call(2).entry, load<uint8>((std_span_data(s.m_data) + k))) and defined(load<uint8>((at(call(2).entry, std_span_data(call(2).parameter(dst))) + k))) }, 1u64); close(); }
            have 2u64 < at(call(2).entry, std_span_size(call(2).parameter(dst))) by { close(); }
            have defined(load<uint8>((std_span_data(call(2).parameter(dst)) + 2u64))) by { instantiate(forall (k: uint64) { 0u64 <= k and k < at(call(2).entry, std_span_size(call(2).parameter(dst))) implies load<uint8>((at(call(2).entry, std_span_data(call(2).parameter(dst))) + k)) == at(call(2).entry, load<uint8>((std_span_data(s.m_data) + k))) and defined(load<uint8>((at(call(2).entry, std_span_data(call(2).parameter(dst))) + k))) }, 2u64); close(); }
            have 3u64 < at(call(2).entry, std_span_size(call(2).parameter(dst))) by { close(); }
            have defined(load<uint8>((std_span_data(call(2).parameter(dst)) + 3u64))) by { instantiate(forall (k: uint64) { 0u64 <= k and k < at(call(2).entry, std_span_size(call(2).parameter(dst))) implies load<uint8>((at(call(2).entry, std_span_data(call(2).parameter(dst))) + k)) == at(call(2).entry, load<uint8>((std_span_data(s.m_data) + k))) and defined(load<uint8>((at(call(2).entry, std_span_data(call(2).parameter(dst))) + k))) }, 3u64); close(); }
            have defined(load<uint8>(((&obj) as (uint8 *)) + 0u64)) by {
                transport(defined(load<uint8>(std_span_data(call(2).parameter(dst)) + 0u64)), defined(load<uint8>(((&obj) as (uint8 *)) + 0u64))) using {
                    ((&obj) as (uint8 *)) == std_span_data(call(2).parameter(dst));
                    defined(load<uint8>(std_span_data(call(2).parameter(dst)) + 0u64));
                };
            }
            have defined(load<uint8>(((&obj) as (uint8 *)) + 1u64)) by {
                transport(defined(load<uint8>(std_span_data(call(2).parameter(dst)) + 1u64)), defined(load<uint8>(((&obj) as (uint8 *)) + 1u64))) using {
                    at(call(2).entry, std_span_data(call(2).parameter(dst))) == ((&obj) as (uint8 *));
                    defined(load<uint8>(std_span_data(call(2).parameter(dst)) + 1u64));
                };
            }
            have defined(load<uint8>(((&obj) as (uint8 *)) + 2u64)) by {
                transport(defined(load<uint8>(std_span_data(call(2).parameter(dst)) + 2u64)), defined(load<uint8>(((&obj) as (uint8 *)) + 2u64))) using {
                    at(call(2).entry, std_span_data(call(2).parameter(dst))) == ((&obj) as (uint8 *));
                    defined(load<uint8>(std_span_data(call(2).parameter(dst)) + 2u64));
                };
            }
            have defined(load<uint8>(((&obj) as (uint8 *)) + 3u64)) by {
                transport(defined(load<uint8>(std_span_data(call(2).parameter(dst)) + 3u64)), defined(load<uint8>(((&obj) as (uint8 *)) + 3u64))) using {
                    at(call(2).entry, std_span_data(call(2).parameter(dst))) == ((&obj) as (uint8 *));
                    defined(load<uint8>(std_span_data(call(2).parameter(dst)) + 3u64));
                };
            }
            have viewable(memory((&obj)[0..1])) by { close(); }
            have defined(load<uint32>(&obj)) by { close(); }

            // Span setup touches local storage. The caller's input bytes remain
            // unchanged up to the reader's call entry.
            have forall (k: uint64) { k < 4u64 implies at(call(2).entry, load<uint8>(std_span_data(s.m_data) + k)) == old(load<uint8>(std_span_data(s.m_data) + k)) } by {
                intro();
                intro();
                have separate(region(0).footprint, at(function.entry, memory((std_span_data(s.m_data) + k)[0]))) by { close(); }
                have at(region(0).exit, load<uint8>(old(std_span_data(s.m_data)) + k)) == at(region(0).entry, load<uint8>(old(std_span_data(s.m_data)) + k)) by {
                    preserve(at(function.entry, memory((std_span_data(s.m_data) + k)[0])), region(0));
                }
                have separate(region(1).footprint, at(function.entry, memory((std_span_data(s.m_data) + k)[0]))) by { close(); }
                have at(region(1).exit, load<uint8>(old(std_span_data(s.m_data)) + k)) == at(region(1).entry, load<uint8>(old(std_span_data(s.m_data)) + k)) by {
                    preserve(at(function.entry, memory((std_span_data(s.m_data) + k)[0])), region(1));
                }
                have separate(region(2).footprint, at(function.entry, memory((std_span_data(s.m_data) + k)[0]))) by { close(); }
                have at(region(2).exit, load<uint8>(old(std_span_data(s.m_data)) + k)) == at(region(2).entry, load<uint8>(old(std_span_data(s.m_data)) + k)) by {
                    preserve(at(function.entry, memory((std_span_data(s.m_data) + k)[0])), region(2));
                }
                have separate(region(3).footprint, at(function.entry, memory((std_span_data(s.m_data) + k)[0]))) by { close(); }
                have at(region(3).exit, load<uint8>(old(std_span_data(s.m_data)) + k)) == at(region(3).entry, load<uint8>(old(std_span_data(s.m_data)) + k)) by {
                    preserve(at(function.entry, memory((std_span_data(s.m_data) + k)[0])), region(3));
                }
                have separate(region(4).footprint, at(function.entry, memory((std_span_data(s.m_data) + k)[0]))) by { close(); }
                have at(region(4).exit, load<uint8>(old(std_span_data(s.m_data)) + k)) == at(region(4).entry, load<uint8>(old(std_span_data(s.m_data)) + k)) by {
                    preserve(at(function.entry, memory((std_span_data(s.m_data) + k)[0])), region(4));
                }
                have separate(region(5).footprint, at(function.entry, memory((std_span_data(s.m_data) + k)[0]))) by { close(); }
                have at(region(5).exit, load<uint8>(old(std_span_data(s.m_data)) + k)) == at(region(5).entry, load<uint8>(old(std_span_data(s.m_data)) + k)) by {
                    preserve(at(function.entry, memory((std_span_data(s.m_data) + k)[0])), region(5));
                }
                have separate(region(6).footprint, at(function.entry, memory((std_span_data(s.m_data) + k)[0]))) by { close(); }
                have at(region(6).exit, load<uint8>(old(std_span_data(s.m_data)) + k)) == at(region(6).entry, load<uint8>(old(std_span_data(s.m_data)) + k)) by {
                    preserve(at(function.entry, memory((std_span_data(s.m_data) + k)[0])), region(6));
                }
                close();
            }

            // Use the byte pointer equality to relate the local word to the input.
            have load<uint8>(((&obj) as (uint8 *)) + 0u64) == at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 0u64)) by {
                instantiate(forall (k: uint64) { 0u64 <= k and k < at(call(2).entry, std_span_size(call(2).parameter(dst))) implies load<uint8>((at(call(2).entry, std_span_data(call(2).parameter(dst))) + k)) == at(call(2).entry, load<uint8>((std_span_data(s.m_data) + k))) and defined(load<uint8>((at(call(2).entry, std_span_data(call(2).parameter(dst))) + k))) }, 0u64);
                transport(load<uint8>(at(call(2).entry, std_span_data(call(2).parameter(dst))) + 0u64) == at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 0u64)), load<uint8>(((&obj) as (uint8 *)) + 0u64) == at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 0u64))) using {
                    at(call(2).entry, std_span_data(call(2).parameter(dst))) == ((&obj) as (uint8 *));
                    load<uint8>(at(call(2).entry, std_span_data(call(2).parameter(dst))) + 0u64) == at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 0u64));
                };
            }
            have at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 0u64)) == old(load<uint8>(std_span_data(s.m_data) + 0u64)) by {
                instantiate(forall (k: uint64) { k < 4u64 implies at(call(2).entry, load<uint8>(std_span_data(s.m_data) + k)) == old(load<uint8>(std_span_data(s.m_data) + k)) }, 0u64);
                close();
            }
            have load<uint8>(((&obj) as (uint8 *)) + 0u64) == old(load<uint8>(std_span_data(s.m_data) + 0u64)) by { close(); }
            have load<uint8>(((&obj) as (uint8 *)) + 1u64) == at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 1u64)) by {
                instantiate(forall (k: uint64) { 0u64 <= k and k < at(call(2).entry, std_span_size(call(2).parameter(dst))) implies load<uint8>((at(call(2).entry, std_span_data(call(2).parameter(dst))) + k)) == at(call(2).entry, load<uint8>((std_span_data(s.m_data) + k))) and defined(load<uint8>((at(call(2).entry, std_span_data(call(2).parameter(dst))) + k))) }, 1u64);
                transport(load<uint8>(at(call(2).entry, std_span_data(call(2).parameter(dst))) + 1u64) == at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 1u64)), load<uint8>(((&obj) as (uint8 *)) + 1u64) == at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 1u64))) using {
                    at(call(2).entry, std_span_data(call(2).parameter(dst))) == ((&obj) as (uint8 *));
                    load<uint8>(at(call(2).entry, std_span_data(call(2).parameter(dst))) + 1u64) == at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 1u64));
                };
            }
            have at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 1u64)) == old(load<uint8>(std_span_data(s.m_data) + 1u64)) by {
                instantiate(forall (k: uint64) { k < 4u64 implies at(call(2).entry, load<uint8>(std_span_data(s.m_data) + k)) == old(load<uint8>(std_span_data(s.m_data) + k)) }, 1u64);
                close();
            }
            have load<uint8>(((&obj) as (uint8 *)) + 1u64) == old(load<uint8>(std_span_data(s.m_data) + 1u64)) by { close(); }
            have load<uint8>(((&obj) as (uint8 *)) + 2u64) == at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 2u64)) by {
                instantiate(forall (k: uint64) { 0u64 <= k and k < at(call(2).entry, std_span_size(call(2).parameter(dst))) implies load<uint8>((at(call(2).entry, std_span_data(call(2).parameter(dst))) + k)) == at(call(2).entry, load<uint8>((std_span_data(s.m_data) + k))) and defined(load<uint8>((at(call(2).entry, std_span_data(call(2).parameter(dst))) + k))) }, 2u64);
                transport(load<uint8>(at(call(2).entry, std_span_data(call(2).parameter(dst))) + 2u64) == at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 2u64)), load<uint8>(((&obj) as (uint8 *)) + 2u64) == at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 2u64))) using {
                    at(call(2).entry, std_span_data(call(2).parameter(dst))) == ((&obj) as (uint8 *));
                    load<uint8>(at(call(2).entry, std_span_data(call(2).parameter(dst))) + 2u64) == at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 2u64));
                };
            }
            have at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 2u64)) == old(load<uint8>(std_span_data(s.m_data) + 2u64)) by {
                instantiate(forall (k: uint64) { k < 4u64 implies at(call(2).entry, load<uint8>(std_span_data(s.m_data) + k)) == old(load<uint8>(std_span_data(s.m_data) + k)) }, 2u64);
                close();
            }
            have load<uint8>(((&obj) as (uint8 *)) + 2u64) == old(load<uint8>(std_span_data(s.m_data) + 2u64)) by { close(); }
            have load<uint8>(((&obj) as (uint8 *)) + 3u64) == at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 3u64)) by {
                instantiate(forall (k: uint64) { 0u64 <= k and k < at(call(2).entry, std_span_size(call(2).parameter(dst))) implies load<uint8>((at(call(2).entry, std_span_data(call(2).parameter(dst))) + k)) == at(call(2).entry, load<uint8>((std_span_data(s.m_data) + k))) and defined(load<uint8>((at(call(2).entry, std_span_data(call(2).parameter(dst))) + k))) }, 3u64);
                transport(load<uint8>(at(call(2).entry, std_span_data(call(2).parameter(dst))) + 3u64) == at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 3u64)), load<uint8>(((&obj) as (uint8 *)) + 3u64) == at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 3u64))) using {
                    at(call(2).entry, std_span_data(call(2).parameter(dst))) == ((&obj) as (uint8 *));
                    load<uint8>(at(call(2).entry, std_span_data(call(2).parameter(dst))) + 3u64) == at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 3u64));
                };
            }
            have at(call(2).entry, load<uint8>(std_span_data(s.m_data) + 3u64)) == old(load<uint8>(std_span_data(s.m_data) + 3u64)) by {
                instantiate(forall (k: uint64) { k < 4u64 implies at(call(2).entry, load<uint8>(std_span_data(s.m_data) + k)) == old(load<uint8>(std_span_data(s.m_data) + k)) }, 3u64);
                close();
            }
            have load<uint8>(((&obj) as (uint8 *)) + 3u64) == old(load<uint8>(std_span_data(s.m_data) + 3u64)) by { close(); }
            // Interpret the copied bytes in the pinned little-endian word layout.
            have load<uint32>(&obj) == old((load<uint8>(std_span_data(s.m_data) + 0u64) as uint32) | (load<uint8>(std_span_data(s.m_data) + 1u64) as uint32) << 8u32 | (load<uint8>(std_span_data(s.m_data) + 2u64) as uint32) << 16u32 | (load<uint8>(std_span_data(s.m_data) + 3u64) as uint32) << 24u32) by {
                rewrite(old(load<uint8>(std_span_data(s.m_data) + 0u64)), load<uint8>(((&obj) as (uint8 *)) + 0u64));
                rewrite(old(load<uint8>(std_span_data(s.m_data) + 1u64)), load<uint8>(((&obj) as (uint8 *)) + 1u64));
                rewrite(old(load<uint8>(std_span_data(s.m_data) + 2u64)), load<uint8>(((&obj) as (uint8 *)) + 2u64));
                rewrite(old(load<uint8>(std_span_data(s.m_data) + 3u64)), load<uint8>(((&obj) as (uint8 *)) + 3u64));
                apply(integer::uint32_from_le_bytes(&obj));
                close();
            }
            // The copied descriptor dies before the endian conversion reads the word.
            step_until(call(3).entry);
            have separate(region(8).footprint, memory((&obj)[0..1])) by { close(); }
            have at(region(8).entry, defined(load<uint32>(&obj))) by { close(); }
            have at(region(8).exit, defined(load<uint32>(&obj))) by { preserve(memory((&obj)[0..1]), region(8)); }
            have defined(load<uint32>(&obj)) by { close(); }
            step();
            step_until(function.exit);
        }
        threw => { }
    }
}
