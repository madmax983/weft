//! The order of the blocks of a body (`docs/ir.md` 5.1.9).
//!
//! The builder makes a join block before the blocks that go to it, so the
//! numbers of the blocks do not follow the control flow. [`renumber`] gives
//! the blocks new numbers in reverse post-order. Then each edge that is not a
//! back edge goes to a block with a larger number, the text of a body reads from
//! top to bottom, and a pass over the blocks in order sees each block after the
//! blocks that go to it (except on a back edge).
//!
//! The depth-first walk visits the successors of a block from the last one to
//! the first one. So the first successor comes right after its block: the next
//! block of a call before its cleanup block, the first arm of a `Switch` before
//! the other arms, the body of a loop before its exit. The cleanup blocks of a
//! frame come after the normal blocks that they serve. The blocks that the entry
//! does not reach (dead code) come last, in their old order, each one with the
//! blocks that only it reaches.

use crate::{id_of, BlockId, Body};

/// Returns the blocks of `body` in the new order: the blocks that the entry
/// reaches in reverse post-order, then the other blocks.
pub fn reverse_post_order(body: &Body) -> Vec<BlockId> {
    let n = body.blocks.len();
    let succs: Vec<Vec<usize>> = body
        .blocks
        .iter()
        .map(|b| {
            b.term
                .kind
                .successors()
                .iter()
                .map(|s| s.index())
                .filter(|&s| s < n)
                .collect()
        })
        .collect();
    let mut seen = vec![false; n];
    let mut out: Vec<BlockId> = Vec::with_capacity(n);
    let roots = std::iter::once(body.entry.index()).chain(0..n);
    for root in roots {
        if root >= n || seen[root] {
            continue;
        }
        // Post-order with an explicit stack: a long chain of blocks must not
        // use the call stack. Each frame holds the count of the successors
        // that the walk did not visit yet; it visits them from the last one.
        let mut post: Vec<usize> = Vec::new();
        let mut stack: Vec<(usize, usize)> = vec![(root, succs[root].len())];
        seen[root] = true;
        while let Some((b, left)) = stack.pop() {
            if left == 0 {
                post.push(b);
                continue;
            }
            stack.push((b, left - 1));
            if let Some(&s) = succs[b].get(left - 1) {
                if !seen[s] {
                    seen[s] = true;
                    stack.push((s, succs[s].len()));
                }
            }
        }
        out.extend(post.into_iter().rev().map(|b| BlockId(id_of(b))));
    }
    out
}

/// Gives the blocks of `body` new numbers in the order of
/// [`reverse_post_order`], and changes each block id in the body to match: the
/// successors of each terminator, the entry and the unwind exit.
pub fn renumber(body: &mut Body) {
    let order = reverse_post_order(body);
    let n = body.blocks.len();
    let mut new_id = vec![BlockId(0); n];
    for (k, b) in order.iter().enumerate() {
        if let Some(x) = new_id.get_mut(b.index()) {
            *x = BlockId(id_of(k));
        }
    }
    let mut map = |b: &mut BlockId| {
        if let Some(&x) = new_id.get(b.index()) {
            *b = x;
        }
    };
    let mut old: Vec<Option<crate::Block>> = std::mem::take(&mut body.blocks)
        .into_iter()
        .map(Some)
        .collect();
    body.blocks = order
        .iter()
        .filter_map(|b| old.get_mut(b.index()).and_then(Option::take))
        .collect();
    for blk in &mut body.blocks {
        blk.term.kind.for_each_block_mut(&mut map);
    }
    map(&mut body.entry);
    map(&mut body.unwind_exit);
}
