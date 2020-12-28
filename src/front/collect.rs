use crate::front;
use crate::front::ast;
use crate::front::cst::{CollectedProgram, TypeStore};
use crate::front::error::Result;

///Collect all items in the program into a format more suitable for following steps.
pub fn collect<'a>(_prog: &'a front::Program<Option<ast::Module>>) -> Result<(TypeStore, CollectedProgram<'a>)> {
    //TODO magical unicorn implementation
    todo!()
}
