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

/// The hasher state of maps whose keys hash as one precomputed `u64`.
pub(crate) type U64BuildHasher = BuildHasherDefault<U64Hasher>;

/// A `HashMap` keyed by a precomputed hash or a dense identity.
pub(crate) type U64Map<V> = std::collections::HashMap<u64, V, U64BuildHasher>;

/// Computes an interner's fingerprint of a key: a hash used only to pick a
/// bucket inside one process, where the bucket then compares keys exactly.
/// It needs no resistance to chosen keys, so each word costs one rotation,
/// one xor and one multiplication instead of a SipHash round.
#[derive(Clone, Copy, Default)]
pub(crate) struct FingerprintHasher(u64);

impl FingerprintHasher {
    fn add(&mut self, word: u64) {
        self.0 = (self.0.rotate_left(5) ^ word).wrapping_mul(0x517C_C1B7_2722_0A95);
    }
}

impl Hasher for FingerprintHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        let (chunks, rest) = bytes.as_chunks::<8>();
        for chunk in chunks {
            self.add(u64::from_le_bytes(*chunk));
        }
        if !rest.is_empty() {
            let mut word = [0u8; 8];
            word[..rest.len()].copy_from_slice(rest);
            // The length keeps `[0]` and `[0, 0]` apart.
            self.add(u64::from_le_bytes(word) ^ ((rest.len() as u64) << 56));
        }
    }

    fn write_u8(&mut self, value: u8) {
        self.add(u64::from(value));
    }

    fn write_u16(&mut self, value: u16) {
        self.add(u64::from(value));
    }

    fn write_u32(&mut self, value: u32) {
        self.add(u64::from(value));
    }

    fn write_u64(&mut self, value: u64) {
        self.add(value);
    }

    fn write_u128(&mut self, value: u128) {
        self.add(value as u64);
        self.add((value >> 64) as u64);
    }

    fn write_usize(&mut self, value: usize) {
        self.add(value as u64);
    }
}

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

    #[test]
    fn fingerprints_separate_nearby_keys() {
        use std::hash::Hash;
        fn fingerprint<T: Hash + ?Sized>(key: &T) -> u64 {
            let mut hasher = FingerprintHasher::default();
            key.hash(&mut hasher);
            hasher.finish()
        }
        let mut seen = std::collections::BTreeSet::new();
        for left in 0..64u32 {
            for right in 0..64u64 {
                assert!(seen.insert(fingerprint(&(left, right, "name"))));
            }
        }
        // Order and byte-string length both matter.
        assert_ne!(fingerprint(&(1u32, 2u32)), fingerprint(&(2u32, 1u32)));
        assert_ne!(fingerprint(&[0u8][..]), fingerprint(&[0u8, 0][..]));
        assert_ne!(fingerprint(&"ab"), fingerprint(&"abc"));
    }
}
