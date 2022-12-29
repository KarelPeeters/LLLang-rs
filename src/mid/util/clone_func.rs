use std::collections::HashMap;

use itertools::Itertools;

use crate::mid::ir::{Block, BlockInfo, Function, FunctionInfo, ParameterInfo, PhiInfo, Program, StackSlotInfo, Value};
use crate::util::zip_eq;

impl Program {
    pub fn deep_clone_function(&mut self, func: Function, replace_args: Option<&[Value]>) -> FunctionInfo {
        let old_info = self.get_func(func);

        let old_params = old_info.params.clone();
        let old_slots = old_info.slots.clone();
        let old_blocks = self.collect_blocks(self.get_func(func).entry.block);

        let mut new_params = vec![];
        let mut map_param = HashMap::new();

        if let Some(replace_args) = replace_args {
            assert_eq!(old_params.len(), replace_args.len());
            for (&old_param, &new_arg) in zip_eq(&old_params, replace_args) {
                let &ParameterInfo { ty } = self.get_param(old_param);
                assert_eq!(ty, self.type_of_value(new_arg));

                assert!(map_param.insert(old_param, new_arg).is_none());
            }
        } else {
            for &old_param in &old_params {
                let &ParameterInfo { ty } = self.get_param(old_param);
                let new_param = self.define_param(ParameterInfo { ty });

                new_params.push(new_param);
                assert!(map_param.insert(old_param, Value::Param(new_param)).is_none());
            }
        };

        let mut new_slots = vec![];
        let map_slot: HashMap<_, _> = old_slots.iter().map(|&old_slot| {
            let &StackSlotInfo { inner_ty, ref debug_name } = self.get_slot(old_slot);
            let new_slot = self.define_slot(StackSlotInfo { inner_ty, debug_name: debug_name.clone() });
            new_slots.push(new_slot);
            (old_slot, new_slot)
        }).collect();

        let mut map_phi = HashMap::new();
        let mut map_instr = HashMap::new();

        let map_block: HashMap<_, _> = old_blocks.iter().map(|&old_block| {
            let old_block_info = self.get_block(old_block);

            let old_phis = old_block_info.phis.clone();
            let old_instrs = old_block_info.instructions.clone();
            // we don't need to do anything extra for terminator, this is already a deep clone
            let new_terminator = old_block_info.terminator.clone();

            let new_phis = old_phis.iter().map(|&old_phi| {
                let &PhiInfo { ty } = self.get_phi(old_phi);
                let new_phy = self.define_phi(PhiInfo { ty });
                assert!(map_phi.insert(old_phi, new_phy).is_none());
                new_phy
            }).collect_vec();
            let new_instructions = old_instrs.iter().map(|&old_instr| {
                let old_instr_info = self.get_instr(old_instr);
                let new_instr_info = old_instr_info.clone();
                let new_instr = self.define_instr(new_instr_info);
                assert!(map_instr.insert(old_instr, new_instr).is_none());
                new_instr
            }).collect_vec();

            let new_block_info = BlockInfo {
                phis: new_phis,
                // TODO map instruction args
                instructions: new_instructions,
                // TODO map terminator blocks and args
                terminator: new_terminator,
            };
            let new_block = self.define_block(new_block_info);
            (old_block, new_block)
        }).collect();

        let map_block_map = map_block;
        let map_block = |block: Block| {
            map_block_map.get(&block).copied().unwrap()
        };

        let map_value = |value: Value| {
            match value {
                Value::Void | Value::Undef(_) | Value::Const(_) | Value::Func(_) | Value::Extern(_) | Value::Data(_) => value,
                Value::Param(param) => map_param.get(&param).copied().unwrap(),
                Value::Slot(slot) => map_slot.get(&slot).copied().unwrap().into(),
                Value::Phi(phi) => map_phi.get(&phi).copied().unwrap().into(),
                Value::Instr(instr) => map_instr.get(&instr).copied().unwrap().into(),
            }
        };
        for &new_instr in map_instr.values() {
            let new_instr = self.get_instr_mut(new_instr);
            new_instr.replace_values(map_value);
        }
        for &new_block in map_block_map.values() {
            let new_term = &mut self.get_block_mut(new_block).terminator;
            new_term.replace_blocks(map_block);
            new_term.replace_values(map_value);
        }

        let old_info = self.get_func(func);

        let new_entry = {
            let mut new_entry = old_info.entry.clone();
            new_entry.replace_blocks(map_block);
            new_entry.replace_values(map_value);
            new_entry
        };

        FunctionInfo {
            ty: old_info.ty,
            func_ty: old_info.func_ty.clone(),
            // we don't inherit the global name, that could results in duplicate symbols
            global_name: None,
            debug_name: old_info.debug_name.clone(),
            entry: new_entry,
            params: new_params,
            slots: new_slots,
        }
    }
}