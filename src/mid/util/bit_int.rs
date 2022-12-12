use static_assertions;

pub type UStorage = u64;
pub type IStorage = i64;
static_assertions::assert_eq_size!(UStorage, IStorage);
const MAX_BITS: u32 = UStorage::BITS as u32;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct BitInt {
    bits: u32,
    value: UStorage,
}

#[derive(Debug, Eq, PartialEq)]
pub struct BitOverflow;

impl BitInt {
    pub fn new(bits: u32, value: UStorage) -> Result<Self, BitOverflow> {
        assert!(bits <= MAX_BITS);
        let bits_used = MAX_BITS - value.leading_zeros();
        if bits_used > bits {
            Err(BitOverflow)
        } else {
            Ok(BitInt { bits, value })
        }
    }

    pub fn new_zero(bits: u32) -> Self {
        // zero cannot overflow
        Self::new(bits, 0).unwrap()
    }

    pub fn new_masked(bits: u32, value: UStorage) -> Self {
        // we cannot overflow here either
        let mask = mask(bits);
        Self::new(bits, value & mask).unwrap()
    }

    pub fn bits(&self) -> u32 {
        self.bits
    }

    /// Get the zero-extended value.
    pub fn unsigned(&self) -> UStorage {
        self.value
    }

    /// Get the sign-extended value.
    pub fn signed(&self) -> IStorage {
        // if we don't have any bits we can't have a sign either
        if self.bits == 0 {
            return 0;
        }

        let bits = self.bits as u32;
        let sign = self.value & (1 << (bits - 1)) != 0;

        if sign {
            let top_mask = !mask(bits);
            (self.value | top_mask) as IStorage
        } else {
            self.value as IStorage
        }
    }

    pub fn is_zero(self) -> bool {
        self.value == 0
    }

    pub fn unwrap_bool(self) -> bool {
        assert!(self.bits == 1);
        self.value != 0
    }
}

fn mask(bits: u32) -> UStorage {
    if bits == UStorage::BITS {
        (-(1 as IStorage)) as UStorage
    } else {
        (1 << bits) - 1
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Binary;

    use crate::mid::util::bit_int::{BitInt, BitOverflow, mask, MAX_BITS, UStorage};

    #[track_caller]
    fn assert_eq_bin<T: Eq + Binary>(left: T, right: T) {
        assert_eq!(format!("{:0b}", left), format!("{:0b}", right));
    }

    #[test]
    fn test_mask() {
        assert_eq_bin(mask(0), 0b00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000);
        assert_eq_bin(mask(1), 0b00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000001);
        assert_eq_bin(mask(7), 0b00000000_00000000_00000000_00000000_00000000_00000000_00000000_01111111);
        assert_eq_bin(mask(32), 0b00000000_00000000_00000000_00000000_11111111_11111111_11111111_11111111);
        assert_eq_bin(mask(33), 0b00000000_00000000_00000000_00000001_11111111_11111111_11111111_11111111);
        assert_eq_bin(mask(63), 0b01111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111);
        assert_eq_bin(mask(64), 0b11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111);
    }

    #[test]
    fn test_overflow() {
        assert_match!(BitInt::new(0, 0b111), Err(BitOverflow));
        assert_match!(BitInt::new(0, 0), Ok(_));
        assert_match!(BitInt::new(16, 1 << 17), Err(BitOverflow));
        assert_match!(BitInt::new(16, 1 << 15), Ok(_));
    }

    #[test]
    fn test_getters_zero() {
        let x = BitInt::new(19, 0).unwrap();
        assert_eq_bin(x.unsigned(), 0);
        assert_eq_bin(x.signed(), 0);
    }

    #[test]
    fn test_getters() {
        let x = BitInt::new(3, 0b111).unwrap();
        assert_eq_bin(x.unsigned(), 7);
        assert_eq_bin(x.signed(), -1);
    }

    #[test]
    fn test_getters_max() {
        let x = BitInt::new(MAX_BITS, 17).unwrap();
        assert_eq_bin(x.unsigned(), 17);
        assert_eq_bin(x.signed(), 17);

        let y = BitInt::new(MAX_BITS, (-1i64) as UStorage).unwrap();
        assert_eq_bin(y.unsigned(), (-1i64) as UStorage);
        assert_eq_bin(y.signed(), -1);
    }
}