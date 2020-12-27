use indexmap::map::IndexMap;

use crate::front::ast;
use crate::front::error::{Error, Result};

#[derive(Debug)]
pub struct Scope<'p, V> {
    parent: Option<&'p Scope<'p, V>>,
    values: IndexMap<String, V>,
}

impl<V> Scope<'_, V> {
    pub fn nest(&self) -> Scope<V> {
        Scope { parent: Some(self), values: Default::default() }
    }

    pub fn declare<'a>(&mut self, id: &'a ast::Identifier, var: V) -> Result<'a, ()> {
        if self.values.insert(id.string.to_owned(), var).is_some() {
            Err(Error::IdentifierDeclaredTwice(id))
        } else {
            Ok(())
        }
    }

    pub fn find<'a>(&self, id: &'a ast::Identifier) -> Result<'a, &V> {
        if let Some(s) = self.values.get(&id.string) {
            Ok(s)
        } else if let Some(p) = self.parent {
            p.find(id)
        } else {
            Err(Error::UndeclaredIdentifier(id))
        }
    }
}

impl<'p, V> Default for Scope<'p, V> {
    fn default() -> Self {
        Self {
            parent: Default::default(),
            values: Default::default(),
        }
    }
}
