
        pub mod left { pub const MOD: u32 = 65521; pub fn read() -> u32 { MOD } }
        pub mod right { pub const MOD: u32 = 7; pub fn read() -> u32 { MOD } }
        pub fn entry() -> usize { const CHUNK_SIZE: usize = 5552 * 4; CHUNK_SIZE }
        pub fn wide() -> usize { const LIMIT: usize = 4294967296; LIMIT }
        pub fn small() -> u8 { const N: u8 = 5 * 4; N }
        pub fn flag() -> bool { const FLAG: bool = true; FLAG }
