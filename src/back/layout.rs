use std::cmp::max;

use crate::mid::ir::{ArrayType, Program, TupleType, Type, TypeInfo};

//TODO cache all of this layout stuff somewhere
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Layout {
    // >= 0, multiple of alignment
    pub size_bytes: u32,
    // >= 1 and a power of two
    pub align_bytes: u32,
}

impl Layout {
    pub fn new(size_bytes: u32, align_bytes: u32) -> Self {
        assert!(size_bytes >= 0, "size must be >= 0, got {}", size_bytes);
        assert!(align_bytes >= 1, "alignment must be >= 1, got {}", align_bytes);
        assert!(align_bytes.count_ones() == 1, "alignment must be a power of two, got {}", align_bytes);
        assert!(size_bytes % align_bytes == 0, "size must be a multiple of alignment, got {} and {}", size_bytes, align_bytes);

        Layout { size_bytes, align_bytes }
    }

    pub fn for_type(prog: &Program, ty: Type) -> Self {
        match prog.get_type(ty) {
            TypeInfo::Void => Layout::new(0, 1),

            TypeInfo::Pointer { .. } | TypeInfo::Func(_) => Layout::new(4, 4),

            TypeInfo::Integer { bits: 1 } => Layout::new(1, 1),
            TypeInfo::Integer { bits: 8 } => Layout::new(1, 1),
            TypeInfo::Integer { bits: 16 } => Layout::new(2, 2),
            TypeInfo::Integer { bits: 32 } => Layout::new(4, 4),
            TypeInfo::Integer { bits: 64 } => Layout::new(8, 8),
            TypeInfo::Integer { bits } => panic!("Integer with {} bits not yet supported", bits),

            &TypeInfo::Array(ArrayType { inner, length }) => {
                let inner = Layout::for_type(prog, inner);
                Layout::new(inner.size_bytes * (length as u32), inner.align_bytes)
            }
            TypeInfo::Tuple(TupleType { fields }) => {
                TupleLayout::for_types(prog, fields.iter().copied()).layout
            }
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
pub struct TupleLayout {
    pub layout: Layout,
    pub offsets: Vec<u32>,
}

impl TupleLayout {
    pub fn for_types(prog: &Program, fields: impl IntoIterator<Item=Type>) -> Self {
        TupleLayout::from_layouts(fields.into_iter().map(|f| Layout::for_type(prog, f)))
    }

    pub fn from_layouts(fields: impl IntoIterator<Item=Layout>) -> Self {
        //TODO this can be optimized to pack tuple fields more compactly, right now this is just left-to-right
        //  when this is changed make sure to change usage sites that depend on the current behaviour (ie. parameters)
        //    or maybe it's fine to transfer parameters more compactly too? not for stdcall ofc
        //TODO zero-sized fields can just get offset 0 and increase the normal alignment

        let mut offsets = Vec::new();
        let mut next_offset = 0;
        let mut alignment = 1;

        for field in fields {
            next_offset = next_multiple(next_offset, field.align_bytes);
            offsets.push(next_offset);

            next_offset += field.size_bytes;

            alignment = max(alignment, field.align_bytes);
        }

        //make sure size is multiple of alignment
        //TODO is there a way to only do this if we're part of an array?
        // what if we're just allocating in a tuple, like here, it really doesn't matter
        let size = next_multiple(next_offset, alignment);

        TupleLayout {
            layout: Layout::new(size, alignment),
            offsets,
        }
    }
}

pub fn next_multiple(x: u32, div: u32) -> u32 {
    assert!(div > 0);
    (x + div - 1) / div * div
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn zero_total_size() {
        let layout = TupleLayout::from_layouts([
            Layout::new(0, 1),
            Layout::new(0, 4),
            Layout::new(0, 2),
        ].iter().copied());

        assert_eq!(TupleLayout {
            layout: Layout::new(0, 4),
            offsets: vec![0, 0, 0],
        }, layout);
    }

    #[test]
    fn mixed() {
        // 0.22 3334 44.. 5555 5555 6...

        let layout = TupleLayout::from_layouts([
            Layout::new(1, 1),
            Layout::new(2, 2),
            Layout::new(3, 1),
            Layout::new(3, 1),
            Layout::new(8, 4),
            Layout::new(1, 1),
        ].iter().copied());

        assert_eq!(TupleLayout {
            layout: Layout::new(24, 4),
            offsets: vec![0, 2, 4, 7, 12, 20],
        }, layout);
    }

    #[test]
    fn single_byte() {
        let layout = TupleLayout::from_layouts([
            Layout::new(1, 1),
        ].iter().copied());

        assert_eq!(TupleLayout {
            layout: Layout::new(1, 1),
            offsets: vec![0],
        }, layout);
    }
}