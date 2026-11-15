//! Addressable storage geometry with NO by-value interpretation.
//!
//! This class can contain uninitialized bytes and pointer representations. It
//! grants no initialized scalar, active union field, provenance, permission or
//! Rust validity fact. Only existing allocation/address/raw-memory operations
//! may use the geometry; all typed value traffic is refused transitively.

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct StorageLayout {
    pub size_bytes: u64,
    pub align_bytes: u64,
}

impl StorageLayout {
    pub const fn new(size_bytes: u64, align_bytes: u64) -> Self {
        Self {
            size_bytes,
            align_bytes,
        }
    }

    /// Geometry only. Zero-sized aligned storage is allowed. A sized object
    /// includes its tail padding, so its size is a multiple of its alignment.
    pub fn is_well_formed(self, pointer_bits: u32) -> bool {
        self.align_bytes.is_power_of_two()
            && self.size_bytes.is_multiple_of(self.align_bytes)
            && self.size_bytes.checked_mul(8).is_some()
            && self.align_bytes.checked_mul(8).is_some()
            && match pointer_bits {
                32 => self.size_bytes <= u64::from(u32::MAX) && self.align_bytes <= (1_u64 << 31),
                64 => true,
                _ => false,
            }
    }
}
