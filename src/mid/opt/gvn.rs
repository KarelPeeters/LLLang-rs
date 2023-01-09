use std::collections::hash_map::Entry;
use std::collections::HashMap;

use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::Program;

/// Removes duplicate values.
/// For now this only works on expressions that are trivially equal.
pub fn gvn(prog: &mut Program) -> bool {
    let use_info = UseInfo::new(prog);

    let mut canonical_expr = HashMap::new();
    let mut replacements = vec![];

    for &expr in use_info.expressions() {
        let expr_info = prog.get_expr(expr);
        match canonical_expr.entry(expr_info) {
            Entry::Occupied(entry) => {
                replacements.push((expr, *entry.get()));
            }
            Entry::Vacant(entry) => {
                entry.insert(expr);
            }
        }
    }

    for &(old, new) in &replacements {
        use_info.replace_value_usages(prog, old.into(), new.into());
    }

    println!("GVN replaced {} duplicate expressions", replacements.len());
    !replacements.is_empty()
}