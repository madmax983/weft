//! Capability environments (`docs/ir.md` 5.1.8).
//!
//! Handlers are lexical, so the builder knows the capability of each effect
//! at each point: the innermost environment of the point that binds the
//! effect gives it. An environment that binds no effect up to the root gives
//! the capability of the row, `CapOperand::Row(E)`: the caller of the
//! function gives it.
//!
//! Plan stage B10 opens the environments of handled bodies and closures.
//! Until then each body is in the root environment `e0`, which binds no
//! effect.

use weft_ir::{CapArgs, CapOperand, EffectId};

use super::Builder;

impl Builder<'_> {
    /// Returns the capability of effect `e` at the current point
    /// (`docs/ir.md` 5.1.8): the place that the innermost environment binds
    /// for `e`, or the capability of the row.
    pub(super) fn cap_of(&self, e: EffectId) -> CapOperand {
        let mut cur = Some(self.cap_env);
        // The parent of an environment is older, so the walk ends; the
        // bound is for a table that is not well formed.
        let mut steps = 0;
        while let Some(id) = cur {
            let Some(env) = self.d.cap_envs.get(id.index()) else {
                break;
            };
            if let Some((_, p)) = env.adds.iter().find(|(x, _)| *x == e) {
                return CapOperand::Local(p.clone());
            }
            cur = env.parent;
            steps += 1;
            if steps > self.d.cap_envs.len() {
                break;
            }
        }
        CapOperand::Row(e)
    }

    /// Returns the capabilities that a call at the current point gives to
    /// its callee: the lexical environment (`docs/ir.md` 5.1.8, 5.34).
    pub(super) const fn cap_args(&self) -> CapArgs {
        CapArgs::Lexical(self.cap_env)
    }
}
