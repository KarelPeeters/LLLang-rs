use fixedbitset::FixedBitSet;

use crate::mid::ir::{Block, Function, Program};
use crate::util::IndexMutTwice;

#[derive(Debug)]
pub struct DomInfo {
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
}
