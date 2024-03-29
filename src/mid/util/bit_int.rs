use std::fmt::{Debug, Display, Formatter};

use static_assertions;

pub type UStorage = u64;
pub type IStorage = i64;
static_assertions::assert_eq_size!(UStorage, IStorage);
const MAX_BITS: u32 = UStorage::BITS;

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct BitInt {
    bits: u32,
    value: UStorage,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct BitOverflow {
    bits: u32,
    unsigned: UStorage,
    signed: IStorage,
}

impl BitInt {
    /// Construct from an unsigned value. All bits above `bits` must be zero.
    pub fn from_unsigned(bits: u32, value: UStorage) -> Result<Self, BitOverflow> {
        assert!(bits <= MAX_BITS);

        if value & !Self::mask(bits) != 0 {
            Err(BitOverflow { bits, unsigned: value, signed: value as IStorage })
        } else {
            Ok(BitInt { bits, value })
        }
    }

    /// Construct from an unsigned value. All bits above `bits` must match the sign value at `bits-1`.µ
    /// As a special case we also allow bits=0 and value=0
    pub fn from_signed(bits: u32, value: IStorage) -> Result<Self, BitOverflow> {
        assert!(bits <= MAX_BITS);
        let value = value as UStorage;

        let sign = if bits == 0 {
            false
        } else {
            value & (1 << (bits - 1)) != 0
        };

        let sign_broadcast = if sign { UStorage::MAX } else { 0 };
        let mask_bits = Self::mask(bits);

        if value & !mask_bits != sign_broadcast & !mask_bits {
            Err(BitOverflow { bits, unsigned: value, signed: value as IStorage })
        } else {
            Ok(BitInt { bits, value: value & mask_bits })
        }
    }

    pub fn zero(bits: u32) -> Self {
        assert!(bits <= MAX_BITS);
        BitInt { bits, value: 0 }
    }

    pub fn from_bool(value: bool) -> Self {
        BitInt { bits: 1, value: u64::from(value) }
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

        let bits = self.bits;
        let sign = self.value & (1 << (bits - 1)) != 0;

        if sign {
            let top_mask = !Self::mask(bits);
            (self.value | top_mask) as IStorage
        } else {
            self.value as IStorage
        }
    }

    pub fn is_zero(self) -> bool {
        self.value == 0
    }

    pub fn as_bool(self) -> Option<bool> {
        if self.bits == 1 {
            Some(self.value != 0)
        } else {
            None
        }
    }

    pub fn mask(bits: u32) -> UStorage {
        if bits == UStorage::BITS {
            (-(1 as IStorage)) as UStorage
        } else {
            (1 << bits) - 1
        }
    }

    pub fn negate(self) -> Self {
        Self::from_signed(self.bits, -self.signed()).unwrap()
    }

    pub fn display_value(self) -> impl Display {
        struct Wrapper(BitInt);

        impl Display for Wrapper {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                if let Some(value) = self.0.as_bool() {
                    write!(f, "{}", value)
                } else if self.0.signed() >= 0 {
                    write!(f, "{}u{}", self.0.unsigned(), self.0.bits())
                } else {
                    write!(f, "{}u{}, {}i{}", self.0.unsigned(), self.0.bits(), self.0.signed(), self.0.bits())
                }
            }
        }

        Wrapper(self)
    }
}

impl Debug for BitInt {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "BitInt({})", self.display_value())
    }
}

#[cfg(test)]
#[allow(clippy::unusual_byte_groupings)]
mod tests {
    use std::fmt::Binary;

    use crate::mid::util::bit_int::{BitInt, BitOverflow, IStorage, MAX_BITS, UStorage};

    #[track_caller]
    fn assert_eq_bin<T: Eq + Binary>(left: T, right: T) {
        assert_eq!(format!("{:0b}", left), format!("{:0b}", right));
    }

    #[test]
    fn test_mask() {
        assert_eq_bin(BitInt::mask(0), 0b00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000);
        assert_eq_bin(BitInt::mask(1), 0b00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000001);
        assert_eq_bin(BitInt::mask(7), 0b00000000_00000000_00000000_00000000_00000000_00000000_00000000_01111111);
        assert_eq_bin(BitInt::mask(32), 0b00000000_00000000_00000000_00000000_11111111_11111111_11111111_11111111);
        assert_eq_bin(BitInt::mask(33), 0b00000000_00000000_00000000_00000001_11111111_11111111_11111111_11111111);
        assert_eq_bin(BitInt::mask(63), 0b01111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111);
        assert_eq_bin(BitInt::mask(64), 0b11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111);
    }

    #[test]
    fn test_overflow_unsigned() {
        assert_match!(BitInt::from_unsigned(0, 0b111), Err(BitOverflow { .. }));
        assert_match!(BitInt::from_unsigned(0, 0), Ok(_));
        assert_match!(BitInt::from_unsigned(0, 1), Err(BitOverflow { .. }));

        assert_match!(BitInt::from_unsigned(16, 1 << 17), Err(BitOverflow { .. }));
        assert_match!(BitInt::from_unsigned(16, 1 << 15), Ok(_));
    }

    #[test]
    fn test_overflow_signed() {
        assert_match!(BitInt::from_signed(32, u32::MAX as IStorage), Err(_))
    }

    #[test]
    fn test_getters_zero() {
        let x = BitInt::from_unsigned(19, 0).unwrap();
        assert_eq_bin(x.unsigned(), 0);
        assert_eq_bin(x.signed(), 0);
    }

    #[test]
    fn test_getters() {
        let x = BitInt::from_unsigned(3, 0b111).unwrap();
        assert_eq_bin(x.unsigned(), 7);
        assert_eq_bin(x.signed(), -1);
    }

    #[test]
    fn test_getters_max() {
        let x = BitInt::from_unsigned(MAX_BITS, 17).unwrap();
        assert_eq_bin(x.unsigned(), 17);
        assert_eq_bin(x.signed(), 17);

        let y = BitInt::from_unsigned(MAX_BITS, (-1i64) as UStorage).unwrap();
        assert_eq_bin(y.unsigned(), (-1i64) as UStorage);
        assert_eq_bin(y.signed(), -1);
    }

    #[test]
    fn test_from_signed() {
        let zero = BitInt::from_signed(4, 0).unwrap();
        assert_eq_bin(zero.signed(), 0);
        assert_eq_bin(zero.unsigned(), 0);

        let neg_one = BitInt::from_signed(4, -1).unwrap();
        assert_eq_bin(neg_one.signed(), -1);
        assert_eq_bin(neg_one.unsigned(), 0b1111);
    }

    #[test]
    fn bool_values() {
        assert_eq!(BitInt::from_bool(false).unsigned(), 0);
        assert_eq!(BitInt::from_bool(false).signed(), 0);
        assert_eq!(BitInt::from_bool(true).unsigned(), 1);
        assert_eq!(BitInt::from_bool(true).signed(), -1);
    }
}