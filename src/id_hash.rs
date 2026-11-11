//! A hasher for maps keyed by a `u64` that is already a hash or a dense
//! identity: an interner's fingerprint, a node id. The standard hasher runs
//! SipHash over such a key a second time, which was about a tenth of a
//! failed search's instructions.

use std::hash::{BuildHasherDefault, Hasher};

/// Spreads one `u64` with a single multiplication. hashbrown takes its
/// bucket from a hash's low bits and its control byte from the top seven, so
/// an odd multiplier keeps sequential ids apart in both.
#[derive(Clone, Copy, Default)]
pub(crate) struct U64Hasher(u64);

impl Hasher for U64Hasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        // Only `u64` keys reach this hasher; anything else is still hashed
        // correctly, one byte at a time.
        for byte in bytes {
            self.write_u64(u64::from(*byte));
        }
    }

    fn write_u64(&mut self, value: u64) {
        self.0 = (self.0.rotate_left(5) ^ value).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    }

    fn write_usize(&mut self, value: usize) {
        self.write_u64(value as u64);
    }
}

/// A `HashMap` keyed by a precomputed hash or a dense identity.
pub(crate) type U64Map<V> = std::collections::HashMap<u64, V, BuildHasherDefault<U64Hasher>>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sequential_and_fingerprint_keys_stay_distinct() {
        let mut map = U64Map::default();
        for key in (0..4096u64).chain((0..4096).map(|key| key << 48)) {
            map.insert(key, key);
        }
        assert_eq!(map.len(), 8191);
        for key in (0..4096u64).chain((0..4096).map(|key| key << 48)) {
            assert_eq!(map.get(&key), Some(&key));
        }
        // The control byte comes from the top seven bits: dense ids must not
        // all share one.
        let tops = (0..128u64)
            .map(|key| {
                let mut hasher = U64Hasher::default();
                hasher.write_u64(key);
                hasher.finish() >> 57
            })
            .collect::<std::collections::BTreeSet<_>>();
        assert!(tops.len() > 32, "{tops:?}");
    }
}
