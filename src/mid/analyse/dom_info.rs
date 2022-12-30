use fixedbitset::FixedBitSet;

use crate::mid::ir::{Block, Function, Program, Scoped, Value};
use crate::util::{IndexMutTwice, VecExt};

#[derive(Debug)]
pub struct DomInfo {
    // TODO make these private with getters at some point
    pub func: Function,
    pub blocks: Vec<Block>,
    successors: Vec<FixedBitSet>,
    dominates: Vec<FixedBitSet>,
    frontier: Vec<FixedBitSet>,
    parent: Vec<Option<usize>>,
}

impl DomInfo {
    //TODO this whole construction is a disaster, replace it with a better algorithm
    // also don't store all of this redundant state
    pub fn new(prog: &Program, func: Function) -> Self {
        let func_info = prog.get_func(func);
        let entry_block = func_info.entry.block;

        let mut blocks = Vec::new();
        prog.visit_blocks(prog.get_func(func).entry.block, |block| blocks.push(block));

        let successors: Vec<FixedBitSet> = blocks.iter().map(|&block| {
            let mut successors = FixedBitSet::with_capacity(blocks.len());
            prog.get_block(block).terminator.for_each_successor(|succ| {
                let si = blocks.iter()
                    .position(|&b| b == succ)
                    .expect("Successor not in blocks");
                successors.set(si, true);
            });
            successors
        }).collect();

        let mut dominated_by: Vec<FixedBitSet> = blocks.iter().enumerate().map(|(bi, &block)| {
            let mut dominates = FixedBitSet::with_capacity(blocks.len());
            if block == entry_block {
                dominates.set(bi, true)
            } else {
                dominates.set_range(.., true);
            }
            dominates
        }).collect();

        //run dominance algorithm
        loop {
            let mut changed = false;

            for bi in 0..blocks.len() {
                for si in successors[bi].ones() {
                    //going trough won't change anything, so just skip it
                    if bi == si { continue; }

                    let (block_dom, succ_dom) = dominated_by.index_mut_twice(bi, si).unwrap();

                    let count_before = succ_dom.count_ones(..);

                    succ_dom.intersect_with(block_dom);
                    succ_dom.set(si, true);

                    let count_after = succ_dom.count_ones(..);
                    if count_before != count_after {
                        changed = true;
                    }
                }
            }

            if !changed { break; }
        }

        //swap
        let dominates: Vec<FixedBitSet> = (0..blocks.len())
            .map(|bi| {
                let mut dominates = FixedBitSet::with_capacity(blocks.len());
                for di in 0..blocks.len() {
                    dominates.set(di, dominated_by[di][bi]);
                }
                dominates
            })
            .collect();

        //calculate the frontier
        let frontier: Vec<FixedBitSet> = (0..blocks.len())
            .map(|bi| {
                let mut frontier = FixedBitSet::with_capacity(blocks.len());
                for pi in dominates[bi].ones() {
                    for fi in successors[pi].ones() {
                        frontier.set(fi, !dominates[bi][fi]);
                    }
                }
                frontier
            })
            .collect();

        //calculate dominator tree
        let parent: Vec<Option<usize>> = (0..blocks.len())
            .map(|bi| {
                (0..blocks.len()).find(|&ci| {
                    //candidate ci must:
                    //  * strictly dominate bi
                    ci != bi && dominates[ci][bi] &&
                        //  * be dominated by all blocks that strictly dominate bi
                        dominated_by[bi].ones().all(|oi| oi == bi || dominates[oi][ci])
                })
            })
            .collect();

        DomInfo {
            func,
            blocks,
            successors,
            dominates,
            frontier,
            parent,
        }
    }

    fn block_index(&self, block: Block) -> usize {
        self.blocks.iter().position(|&b| b == block)
            .expect("Block not found")
    }

    pub fn is_dominator(&self, dominator: Block, block: Block) -> bool {
        self.dominates[self.block_index(dominator)]
            .contains(self.block_index(block))
    }

    pub fn is_strict_dominator(&self, dominator: Block, block: Block) -> bool {
        dominator != block &&
            self.dominates[self.block_index(dominator)]
                .contains(self.block_index(block))
    }

    pub fn iter_dominated_by(&self, dominator: Block) -> impl Iterator<Item=Block> + '_ {
        self.dominates[self.block_index(dominator)]
            .ones()
            .map(move |bi| self.blocks[bi])
    }

    pub fn iter_dominator_frontier(&self, dominator: Block) -> impl Iterator<Item=Block> + '_ {
        self.frontier[self.block_index(dominator)]
            .ones()
            .map(move |bi| self.blocks[bi])
    }

    pub fn parent(&self, block: Block) -> Option<Block> {
        self.parent[self.block_index(block)].map(|i| self.blocks[i])
    }

    /// Iterate upwards trough the dominator tree, includes both the block itself and the entry block
    pub fn iter_domtree(&self, block: Block) -> impl Iterator<Item=Block> + '_ {
        std::iter::successors(Some(self.block_index(block)), move |&i| self.parent[i])
            .map(move |bi| self.blocks[bi])
    }

    pub fn iter_predecessors(&self, block: Block) -> impl Iterator<Item=Block> + '_ {
        let bi = self.block_index(block);
        (0..self.blocks.len())
            .filter(move |&pi| self.successors[pi][bi])
            .map(move |pi| self.blocks[pi])
    }

    /// Whether `define` strictly dominates `user`.
    /// For values this corresponds to whether values defined at `define` are available as arguments at `user`.
    pub fn pos_is_strict_dominator(&self, define: DomPosition, user: DomPosition) -> bool {
        // things defined in different functions never dominate each other
        if let (Some(d_func), Some(u_func)) = (define.function(), user.function()) {
            if d_func != u_func {
                return false;
            }
        }

        match (define, user) {
            // global dominates everything and nothing else dominates the entry
            (DomPosition::Global, _) => true,
            (_, DomPosition::Global) => false,

            // the same is true for the entry (if the function matches, which it does)
            (DomPosition::FuncEntry(_), _) => true,
            (_, DomPosition::FuncEntry(_)) => false,

            // an "instruction" dominates if it's earlier in the same block or if the block strictly dominates
            (DomPosition::InBlock(_, d_block, d_index), DomPosition::InBlock(_, u_block, u_index)) => {
                (d_block == u_block && d_index < u_index) || self.is_strict_dominator(d_block, u_block)
            }
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum DomPosition {
    Global,
    FuncEntry(Function),
    InBlock(Function, Block, BlockPosition),
}

#[derive(Debug)]
pub struct NoDefFound;

impl DomPosition {
    // TODO find a faster way to do this
    //   maybe the only solution is to keep track of this for each value? that's pretty ugly and brittle...
    pub fn find_def_slow(prog: &Program, func: Function, value: Value) -> Result<Self, NoDefFound> {
        let func_info = prog.get_func(func);

        match value {
            Value::Global(_) | Value::Immediate(_) => {
                Ok(DomPosition::Global)
            }
            Value::Scoped(value) => {
                match value {
                    Scoped::Param(param) => {
                        func_info.params.contains(&param).then_some(DomPosition::FuncEntry(func)).ok_or(NoDefFound)
                    }
                    Scoped::Slot(slot) => {
                        func_info.slots.contains(&slot).then_some(DomPosition::FuncEntry(func)).ok_or(NoDefFound)
                    }
                    Scoped::Phi(phi) => {
                        prog.try_visit_blocks(func_info.entry.block, |block| {
                            let block_info = prog.get_block(block);
                            if block_info.phis.contains(&phi) {
                                Err(DomPosition::InBlock(func, block, BlockPosition::Entry))
                            } else {
                                Ok(())
                            }
                        }).err().ok_or(NoDefFound)
                    }
                    Scoped::Instr(instr) => {
                        prog.try_visit_blocks(func_info.entry.block, |block| {
                            let block_info = prog.get_block(block);
                            if let Some(index) = block_info.instructions.index_of(&instr) {
                                Err(DomPosition::InBlock(func, block, BlockPosition::Instruction(index)))
                            } else {
                                Ok(())
                            }
                        }).err().ok_or(NoDefFound)
                    }
                }
            }
        }
    }
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub enum BlockPosition {
    // Ord is derived correctly, the top element is the lowest one
    Entry,
    Instruction(usize),
    Terminator,
}

impl DomPosition {
    fn function(self) -> Option<Function> {
        match self {
            DomPosition::Global => None,
            DomPosition::FuncEntry(func) => Some(func),
            DomPosition::InBlock(func, _, _) => Some(func),
        }
    }
}
