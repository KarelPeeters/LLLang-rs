use std::fmt::Debug;

use indexmap::IndexMap;
use itertools::Itertools;

use crate::mid::ir::CallingConvention;

pub mod pos;
pub mod ast;
pub mod cst;

pub mod error;
pub mod scope;
pub mod type_solver;

pub mod parser;
pub mod resolve;
pub mod lower;
pub mod type_func;
pub mod lower_func;

const DEFAULT_CALLING_CONVENTION: CallingConvention = CallingConvention::Win64;

#[derive(Debug)]
pub struct Program<C> {
    pub ptr_size_bits: u32,
    pub root: Module<C>,
}

#[derive(Debug, Default)]
pub struct Module<C> {
    pub content: C,
    pub submodules: IndexMap<String, Module<C>>,
}

impl<C> Program<C> {
    pub fn new(ptr_size_bits: u32) -> Self where C: Default {
        Program { ptr_size_bits, root: Module::default() }
    }

    pub fn find_or_create_module(&mut self, path: Vec<String>) -> &mut Module<C> where C: Default {
        path.into_iter().fold(&mut self.root, |a, elem|
            a.submodules.entry(elem).or_default(),
        )
    }

    ///Recursively map module contents to return a new, transformed program
    pub fn try_map<'s, R, E>(&'s self, f: &mut impl FnMut(&'s Module<C>) -> Result<R, E>) -> Result<Program<R>, E> {
        Ok(Program {
            ptr_size_bits: self.ptr_size_bits,
            root: self.root.try_map(f)?,
        })
    }

    ///Run some code for each module in this program
    pub fn try_for_each<'s, E>(&'s self, f: &mut impl FnMut(&'s Module<C>) -> Result<(), E>) -> Result<(), E> {
        self.root.try_for_each(f)
    }
}

impl<C> Module<C> {
    fn try_map<'s, R, E>(&'s self, f: &mut impl FnMut(&'s Self) -> Result<R, E>) -> Result<Module<R>, E> where C: 's {
        Ok(Module {
            content: f(self)?,
            submodules: self.submodules.iter()
                .map(|(k, v)| Ok((k.clone(), v.try_map(f)?)))
                .try_collect()?,
        })
    }

    fn try_for_each<'s, E>(&'s self, f: &mut impl FnMut(&'s Module<C>) -> Result<(), E>) -> Result<(), E> {
        f(self)?;
        self.submodules.values().try_for_each(|v| v.try_for_each(f))?;
        Ok(())
    }
}
