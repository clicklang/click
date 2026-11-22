import click::bytes;
import click::separation;
verifying "bitcoin-src/src/streams.h";
void SpanReader::read(std::span<std::byte> dst) throws std::ios_base::failure {
    owns this->m_data;
    views std_span_data(this->m_data)[0..std_span_size(this->m_data)];
    owns uninitialized(std_span_data(dst)[0..std_span_size(dst)]);
    ensures old(std_span_size(dst)) <= old(std_span_size(this->m_data));
    ensures std_span_data(this->m_data) == old(std_span_data(this->m_data)) + old(std_span_size(dst));
    ensures std_span_size(this->m_data) == old(std_span_size(this->m_data)) - old(std_span_size(dst));
    ensures forall (k: uint64) { 0u64 <= k and k < old(std_span_size(dst)) implies load<uint8>((old(std_span_data(dst)) + k)) == old(load<uint8>((std_span_data(this->m_data) + k))) };
    exceptional ensures old(std_span_size(this->m_data)) < old(std_span_size(dst));
    exceptional ensures std_span_data(this->m_data) == old(std_span_data(this->m_data));
    exceptional ensures std_span_size(this->m_data) == old(std_span_size(this->m_data));
} by {
    mark inputs;
    // The pinned span descriptor has two adjacent eight-byte fields.
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
    step();
    step();
    branch {
        true => {
            step();
            have old(std_span_size(dst)) == 0u64 by { solve(); }
            have forall (k: uint64) { 0u64 <= k and k < old(std_span_size(dst)) implies load<uint8>((old(std_span_data(dst)) + k)) == old(load<uint8>((std_span_data(this->m_data) + k))) } by {
                intro();
                intro();
                have old(std_span_size(dst)) <= k by {
                    rewrite(old(std_span_size(dst)), 0u64);
                    normalize();
                }
                contradiction(k < old(std_span_size(dst)));
            }
        }
        false => {}
    }
    step();
    step();
    branch { true => { step_until(function.exit); } false => {} }
    let { result: output_pointer } = step();
    step();
    let { result: copy_size } = step();
    have call(6).result == call(1).result by { solve(); }
    have call(2).result == old(std_span_size(this->m_data)) by { known(); }
    have call(1).result <= call(2).result by { known(); }
    have call(5).result == old(std_span_data(this->m_data)) by { known(); }
    step() {
        requires forall (k: uint64) { 0u64 <= k and k < call(6).result implies defined(load<uint8>((call(5).result + k))) } by {
            intro();
            intro();
            have k < old(std_span_size(this->m_data)) by { solve(); }
            instantiate(at(function.entry, forall (i: uint64) { 0u64 <= i and i < std_span_size(this->m_data) implies defined(load<uint8>((std_span_data(this->m_data) + i))) }), k);
            rewrite(call(5).result, old(std_span_data(this->m_data)));
            known();
        }
        requires separate(memory(((output_pointer as (void *)) as (uint8 *))[0u64..copy_size]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))])) by {
            have separate(memory(at(inputs, std_span_data(dst))[0u64..at(inputs, std_span_size(dst))]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))])) by { known(); }
            have contains(memory(at(inputs, std_span_data(dst))[0u64..at(inputs, std_span_size(dst))]), memory(((output_pointer as (void *)) as (uint8 *))[0u64..copy_size])) by {
                have output_pointer == at(inputs, std_span_data(dst)) by { known(); }
                have copy_size == at(inputs, std_span_size(dst)) by { solve(); }
                rewrite(output_pointer, at(inputs, std_span_data(dst)));
                rewrite(copy_size, at(inputs, std_span_size(dst)));
                normalize();
            }
            have contains(memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))])) by {
                apply(click::separation::contains_refl(memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))]))) using {};
            }
            apply(click::separation::separate_restrict(memory(at(inputs, std_span_data(dst))[0u64..at(inputs, std_span_size(dst))]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))]), memory(((output_pointer as (void *)) as (uint8 *))[0u64..copy_size]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))]))) using {
                separate(memory(at(inputs, std_span_data(dst))[0u64..at(inputs, std_span_size(dst))]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))]));
                contains(memory(at(inputs, std_span_data(dst))[0u64..at(inputs, std_span_size(dst))]), memory(((output_pointer as (void *)) as (uint8 *))[0u64..copy_size]));
                contains(memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))]), memory(old(std_span_data(this->m_data))[0u64..old(std_span_size(this->m_data))]));
            };
        }
    }
    mark copied;
    // Keep the memcpy byte equality before the subspan and assignment calls.
    have forall (k: uint64) { 0u64 <= k and k < call(6).result implies load<uint8>((call(4).result + (0u64 + k))) == at(call(memcpy, 0).entry, load<uint8>((call(5).result + (0u64 + k)))) } by {
        known();
    }
    have separate(memory((this as (int32 *))[0..2]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result])) by { known(); }
    have separate(memory((byte_offset(this, 8) as (uint64 *))[0..1]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result])) by { known(); }
    have separate(memory((this as (uint8 *))[0..8]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result])) by {
        known();
    }
    have separate(memory((this as (uint8 *))[8..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result])) by {
        known();
    }
    have separate(memory((this as (uint8 *))[0..8]) * memory((this as (uint8 *))[8..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result])) by {
        apply(separation::separate_star(memory((this as (uint8 *))[0..8]), memory((this as (uint8 *))[8..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]))) using {
            separate(memory((this as (uint8 *))[0..8]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]));
            separate(memory((this as (uint8 *))[8..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]));
        };
    }
    have contains(memory(at(call(4).exit, call(4).result)[0u64..call(6).result]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result])) by { apply(separation::contains_refl(memory(at(call(4).exit, call(4).result)[0u64..call(6).result]))) using {}; }
    have separate(memory((this as (uint8 *))[0..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result])) by {
        apply(separation::separate_restrict(memory((this as (uint8 *))[0..8]) * memory((this as (uint8 *))[8..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]), memory((this as (uint8 *))[0..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]))) using {
            separate(memory((this as (uint8 *))[0..8]) * memory((this as (uint8 *))[8..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]));
            contains(memory((this as (uint8 *))[0..8]) * memory((this as (uint8 *))[8..16]), memory((this as (uint8 *))[0..16]));
            contains(memory(at(call(4).exit, call(4).result)[0u64..call(6).result]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]));
        };
    }
    have separate(memory(at(copied, (dst as (uint8 *)))[0..8]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result])) by { known(); }
    have separate(memory(at(copied, (dst as (uint8 *)))[8..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result])) by { known(); }
    have separate(memory(at(copied, (dst as (uint8 *)))[0..8]) * memory(at(copied, (dst as (uint8 *)))[8..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result])) by {
        apply(separation::separate_star(memory(at(copied, (dst as (uint8 *)))[0..8]), memory(at(copied, (dst as (uint8 *)))[8..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]))) using {
            separate(memory(at(copied, (dst as (uint8 *)))[0..8]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]));
            separate(memory(at(copied, (dst as (uint8 *)))[8..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]));
        };
    }
    have contains(memory(at(copied, (dst as (uint8 *)))[0..8]) * memory(at(copied, (dst as (uint8 *)))[8..16]), memory(at(copied, (dst as (uint8 *)))[0..16])) by {
        apply(separation::contains_joined_ranges(at(copied, (dst as (uint8 *))), 0, 8, 16)) using { 0 <= 8; 8 <= 16; };
    }
    have separate(memory(at(copied, (dst as (uint8 *)))[0..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result])) by {
        apply(separation::separate_restrict(memory(at(copied, (dst as (uint8 *)))[0..8]) * memory(at(copied, (dst as (uint8 *)))[8..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]), memory(at(copied, (dst as (uint8 *)))[0..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]))) using {
            separate(memory(at(copied, (dst as (uint8 *)))[0..8]) * memory(at(copied, (dst as (uint8 *)))[8..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]));
            contains(memory(at(copied, (dst as (uint8 *)))[0..8]) * memory(at(copied, (dst as (uint8 *)))[8..16]), memory(at(copied, (dst as (uint8 *)))[0..16]));
            contains(memory(at(call(4).exit, call(4).result)[0u64..call(6).result]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]));
        };
    }
    step_until(region(19).entry);
    have separate(memory(at(region(18).exit, region(18).result)[0..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result])) by { known(); }
    step_until(function.exit);
    have old(std_span_size(dst)) == call(6).result by { solve(); }
    // Transport one destination byte across each later write.
    have forall (k: uint64) { 0u64 <= k and k < old(std_span_size(dst)) implies load<uint8>((old(std_span_data(dst)) + k)) == old(load<uint8>((std_span_data(this->m_data) + k))) } by {
        intro();
        intro();
        have k < call(6).result by {
            rewrite(call(6).result, old(std_span_size(dst)));
            known();
        }
        instantiate(at(copied, forall (j: uint64) { 0u64 <= j and j < call(6).result implies load<uint8>((call(4).result + (0u64 + j))) == at(call(memcpy, 0).entry, load<uint8>((call(5).result + (0u64 + j)))) }), k);
        have contains(memory(at(call(4).exit, call(4).result)[0u64..call(6).result]), memory(at(call(4).exit, call(4).result)[k])) by {
            apply(separation::contains_element(at(call(4).exit, call(4).result), 0u64, call(6).result, k)) using { 0u64 <= k; k < call(6).result; };
        }
        have contains(memory((this as (uint8 *))[0..16]), memory((this as (uint8 *))[0..16])) by { apply(separation::contains_refl(memory((this as (uint8 *))[0..16]))) using {}; }
        have separate(memory((this as (uint8 *))[0..16]), memory(at(call(4).exit, call(4).result)[k])) by {
            apply(separation::separate_restrict(memory((this as (uint8 *))[0..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]), memory((this as (uint8 *))[0..16]), memory(at(call(4).exit, call(4).result)[k]))) using {
                separate(memory((this as (uint8 *))[0..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]));
                contains(memory((this as (uint8 *))[0..16]), memory((this as (uint8 *))[0..16]));
                contains(memory(at(call(4).exit, call(4).result)[0u64..call(6).result]), memory(at(call(4).exit, call(4).result)[k]));
            };
        }
        have separate(region(19).footprint, memory(at(call(4).exit, call(4).result)[k])) by {
            normalize() using { separate(memory((this as (uint8 *))[0..16]), memory(at(call(4).exit, call(4).result)[k])); };
        }
        have at(region(19).exit, load<uint8>((call(4).result + k))) == at(region(19).entry, load<uint8>((call(4).result + k))) by {
            preserve(memory(at(call(4).exit, call(4).result)[k]), region(19));
        }
        have at(call(memcpy, 0).entry, load<uint8>((old(std_span_data(this->m_data)) + k))) == at(call(memcpy, 0).entry, load<uint8>((call(5).result + k))) by {
            rewrite(call(5).result, old(std_span_data(this->m_data)));
            normalize();
        }
        have at(call(memcpy, 0).entry, load<uint8>((old(std_span_data(this->m_data)) + k))) == old(load<uint8>((std_span_data(this->m_data) + k))) by {
            known();
        }
        have contains(memory(at(region(18).exit, region(18).result)[0..16]), memory(at(region(18).exit, region(18).result)[0..16])) by { apply(separation::contains_refl(memory(at(region(18).exit, region(18).result)[0..16]))) using {}; }
        have separate(memory(at(region(18).exit, region(18).result)[0..16]), memory(at(call(4).exit, call(4).result)[k])) by {
            apply(separation::separate_restrict(memory(at(region(18).exit, region(18).result)[0..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]), memory(at(region(18).exit, region(18).result)[0..16]), memory(at(call(4).exit, call(4).result)[k]))) using {
                separate(memory(at(region(18).exit, region(18).result)[0..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]));
                contains(memory(at(region(18).exit, region(18).result)[0..16]), memory(at(region(18).exit, region(18).result)[0..16]));
                contains(memory(at(call(4).exit, call(4).result)[0u64..call(6).result]), memory(at(call(4).exit, call(4).result)[k]));
            };
        }
        have separate(region(16).footprint, memory(at(call(4).exit, call(4).result)[k])) by { normalize() using { separate(memory(at(region(18).exit, region(18).result)[0..16]), memory(at(call(4).exit, call(4).result)[k])); }; }
        have at(region(16).exit, load<uint8>((call(4).result + k))) == at(region(16).entry, load<uint8>((call(4).result + k))) by {
            preserve(memory(at(call(4).exit, call(4).result)[k]), region(16));
        }
        have separate(region(18).footprint, memory(at(call(4).exit, call(4).result)[k])) by { normalize() using { separate(memory(at(region(18).exit, region(18).result)[0..16]), memory(at(call(4).exit, call(4).result)[k])); }; }
        have at(region(18).exit, load<uint8>((call(4).result + k))) == at(region(18).entry, load<uint8>((call(4).result + k))) by {
            preserve(memory(at(call(4).exit, call(4).result)[k]), region(18));
        }
        have separate(region(20).footprint, memory(at(call(4).exit, call(4).result)[k])) by { normalize() using { separate(memory(at(region(18).exit, region(18).result)[0..16]), memory(at(call(4).exit, call(4).result)[k])); }; }
        have at(region(20).exit, load<uint8>((call(4).result + k))) == at(region(20).entry, load<uint8>((call(4).result + k))) by {
            preserve(memory(at(call(4).exit, call(4).result)[k]), region(20));
        }
        have contains(memory(at(copied, (dst as (uint8 *)))[0..16]), memory(at(copied, (dst as (uint8 *)))[0..16])) by { apply(separation::contains_refl(memory(at(copied, (dst as (uint8 *)))[0..16]))) using {}; }
        have separate(memory(at(copied, (dst as (uint8 *)))[0..16]), memory(at(call(4).exit, call(4).result)[k])) by {
            apply(separation::separate_restrict(memory(at(copied, (dst as (uint8 *)))[0..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]), memory(at(copied, (dst as (uint8 *)))[0..16]), memory(at(call(4).exit, call(4).result)[k]))) using {
                separate(memory(at(copied, (dst as (uint8 *)))[0..16]), memory(at(call(4).exit, call(4).result)[0u64..call(6).result]));
                contains(memory(at(copied, (dst as (uint8 *)))[0..16]), memory(at(copied, (dst as (uint8 *)))[0..16]));
                contains(memory(at(call(4).exit, call(4).result)[0u64..call(6).result]), memory(at(call(4).exit, call(4).result)[k]));
            };
        }
        have separate(region(21).footprint, memory(at(call(4).exit, call(4).result)[k])) by {
            normalize() using { separate(memory(at(copied, (dst as (uint8 *)))[0..16]), memory(at(call(4).exit, call(4).result)[k])); };
        }
        have at(region(21).exit, load<uint8>((call(4).result + k))) == at(region(21).entry, load<uint8>((call(4).result + k))) by {
            preserve(memory(at(call(4).exit, call(4).result)[k]), region(21));
        }
        have old(std_span_data(dst)) == call(4).result by { known(); }
        rewrite(old(std_span_data(dst)), call(4).result);
        known();
    }
}
