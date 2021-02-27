use std::cmp::max;

use crate::mid::ir::{Program, Type, TypeInfo};

//TODO cache all of this layout stuff somewhere
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Layout {
    // >= 0
    pub size: i32,

    // >= 1 and a power of two
    pub alignment: i32,
}

impl Layout {
    pub fn from(prog: &Program, ty: Type) -> Self {
        match prog.get_type(ty) {
            TypeInfo::Void => Layout { size: 0, alignment: 1 },

            TypeInfo::Pointer { .. } | TypeInfo::Func(_) => Layout { size: 4, alignment: 4 },

            TypeInfo::Integer { bits: 32 } => Layout { size: 4, alignment: 4 },
            //TODO what should 16 bit alignment be?
            TypeInfo::Integer { bits: 16 } => Layout { size: 2, alignment: 2 },
            TypeInfo::Integer { bits: 8 } => Layout { size: 1, alignment: 1 },
            TypeInfo::Integer { bits: 1 } => Layout { size: 1, alignment: 1 },
            TypeInfo::Integer { bits } => panic!("Integer with {} bits not yet supported", bits),

            TypeInfo::Tuple(info) => {
                TupleLayout::from_types(prog, info.fields.iter().copied()).layout
            }
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
pub struct TupleLayout {
    pub layout: Layout,
    pub offsets: Vec<i32>,
}

impl TupleLayout {
    pub fn from_types(prog: &Program, fields: impl IntoIterator<Item=Type>) -> Self {
        TupleLayout::from_layouts(fields.into_iter().map(|f| Layout::from(prog, f)))
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
            next_offset = next_multiple(next_offset, field.alignment);
            offsets.push(next_offset);

            next_offset += field.size;

            alignment = max(alignment, field.alignment);
        }

        TupleLayout {
            layout: Layout {
                size: next_offset,
                alignment,
            },
            offsets,
        }
    }
}

pub fn next_multiple(x: i32, div: i32) -> i32 {
    assert!(div > 0);
    (x + div - 1) / div * div
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn zero_total_size() {
        let layout = TupleLayout::from_layouts([
            Layout { size: 0, alignment: 1 },
            Layout { size: 0, alignment: 4 },
            Layout { size: 0, alignment: 2 },
        ].iter().copied());

        assert_eq!(TupleLayout {
            layout: Layout { size: 0, alignment: 4 },
            offsets: vec![0, 0, 0],
        }, layout);
    }

    #[test]
    fn mixed() {
        // 0.12 2233 3... 4

        let layout = TupleLayout::from_layouts([
            Layout { size: 1, alignment: 1 },
            Layout { size: 1, alignment: 2 },
            Layout { size: 3, alignment: 1 },
            Layout { size: 3, alignment: 1 },
            Layout { size: 1, alignment: 4 },
        ].iter().copied());

        assert_eq!(TupleLayout {
            layout: Layout { size: 13, alignment: 4 },
            offsets: vec![0, 2, 3, 6, 12],
        }, layout);
    }

    #[test]
    fn single_byte() {
        let layout = TupleLayout::from_layouts([
            Layout { size: 1, alignment: 1 },
        ].iter().copied());

        assert_eq!(TupleLayout {
            layout: Layout { size: 1, alignment: 1 },
            offsets: vec![0],
        }, layout);
    }
}