use std::collections::HashMap;
use std::fmt::Debug;

use itertools::Itertools;

//TODO reorganise the module tree and rename some of them
pub mod pos;
pub mod ast;
pub mod cst;

pub mod error;
pub mod scope;

pub mod parser;
pub mod resolve;
pub mod lower;
pub mod lower_func;
pub mod type_solver;

//TODO rename <- why is this comment here?
//TODO inline generic arg? are there multiple actually used?
#[derive(Debug, Default)]
pub struct Program<C> {
    pub root: Module<C>,
}

impl<C> Program<C> {
    //TODO maybe move this somewhere else? this is only used in main.rs
    //   meh, hypothetically this could be used by all programs that want to build modules
    pub fn find_or_create_module(&mut self, path: Vec<String>) -> &mut Module<C> where C: Default {
        path.into_iter().fold(&mut self.root, |a, elem|
            a.submodules.entry(elem).or_default(),
        )
    }
}

//TODO maybe remove all of this crap?
impl<C> Program<C> {
    ///Recursively map module contents to return a new, transformed program
    pub fn try_map<'s, R, E>(&'s self, f: &mut impl FnMut(&'s Module<C>) -> Result<R, E>) -> Result<Program<R>, E> {
        Ok(Program { root: self.root.try_map(f)? })
    }

    ///Run some code for each module in this program
    pub fn try_for_each<'s, E>(&'s self, f: &mut impl FnMut(&'s Module<C>) -> Result<(), E>) -> Result<(), E> {
        self.root.try_for_each(f)
    }
}


//TODO remove all hashmaps again for determinism
#[derive(Debug, Default)]
pub struct Module<C> {
    pub submodules: HashMap<String, Module<C>>,
    pub content: C,
}

//TODO move the call to f before the child calls, that's more elegant
impl<C> Module<C> {
    fn try_map<'s, R, E>(&'s self, f: &mut impl FnMut(&'s Self) -> Result<R, E>) -> Result<Module<R>, E> where C: 's {
        //TODO is there a way to collect into map without rehashing?
        Ok(Module {
            submodules: self.submodules.iter()
                .map(|(k, v)| Ok((k.clone(), v.try_map(f)?)))
                .try_collect()?,
            content: f(self)?,
        })
    }

    fn try_for_each<'s, E>(&'s self, f: &mut impl FnMut(&'s Module<C>) -> Result<(), E>) -> Result<(), E> {
        self.submodules.values().try_for_each(|v| v.try_for_each(f))?;
        f(self)?;
        Ok(())
    }
}
