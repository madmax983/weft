//! Verified state machines for one-shot continuations and linear values.
//!
//! The interpreter uses these types at run time. The proofs show that a `once`
//! continuation resumes at most once, and that a linear value ends consumed or
//! aborted exactly once.
//!
//! `proofs/link` includes this file. It proves that these state machines refine
//! the continuation and resource records of the effects model
//! (`proofs/link/src/lifecycle_link.rs`). Run `proofs/link/verify.sh` after a
//! change to a spec in this file.

use vstd::prelude::*;

verus! {

/// The state of a captured continuation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ContState {
    /// Captured and not used.
    Fresh,
    /// Resumed at least once.
    Resumed,
    /// Dropped without a resume: the computation aborted.
    Dropped,
}

/// Why a continuation operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ContError {
    /// A `once` continuation was resumed a second time.
    AlreadyResumed,
    /// The continuation was dropped before.
    AlreadyDropped,
}

/// A continuation handle with its affinity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Continuation {
    /// The current state.
    pub state: ContState,
    /// True if the operation is `multi`.
    pub multi: bool,
}

impl Continuation {
    /// Makes a fresh continuation.
    pub fn new(multi: bool) -> (r: Self)
        ensures
            r.state == ContState::Fresh,
            r.multi == multi,
    {
        Self { state: ContState::Fresh, multi }
    }

    /// Records a resume. A `once` continuation accepts only one resume.
    pub fn resume(&mut self) -> (r: Result<(), ContError>)
        ensures
            final(self).multi == old(self).multi,
            old(self).state == ContState::Dropped ==> r == Err::<(), ContError>(
                ContError::AlreadyDropped,
            ) && *final(self) == *old(self),
            old(self).state == ContState::Resumed && !old(self).multi ==> r == Err::<(), ContError>(
                ContError::AlreadyResumed,
            ) && *final(self) == *old(self),
            r is Ok <==> (old(self).state == ContState::Fresh || (old(self).state
                == ContState::Resumed && old(self).multi)),
            r is Ok ==> final(self).state == ContState::Resumed,
    {
        match self.state {
            ContState::Dropped => Err(ContError::AlreadyDropped),
            ContState::Resumed if !self.multi => Err(ContError::AlreadyResumed),
            _ => {
                self.state = ContState::Resumed;
                Ok(())
            },
        }
    }

    /// Records a drop. Returns true if the drop aborts the computation: the
    /// continuation was never resumed.
    pub fn drop_now(&mut self) -> (aborts: bool)
        ensures
            aborts == (old(self).state == ContState::Fresh),
            aborts ==> final(self).state == ContState::Dropped,
            !aborts ==> *final(self) == *old(self),
    {
        match self.state {
            ContState::Fresh => {
                self.state = ContState::Dropped;
                true
            },
            _ => false,
        }
    }
}

/// The state of a linear value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LinState {
    /// Created and not yet finished.
    Live,
    /// Consumed on the normal path.
    Consumed,
    /// Finished by `on abort` during unwinding.
    Aborted,
}

/// A linear value's run-time record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Linear {
    /// The current state.
    pub state: LinState,
}

/// Why a linear operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LinError {
    /// The value is already consumed or aborted.
    NotLive,
}

impl Linear {
    /// Makes a live linear value.
    pub fn new() -> (r: Self)
        ensures
            r.state == LinState::Live,
    {
        Self { state: LinState::Live }
    }

    /// Consumes the value on the normal path.
    pub fn consume(&mut self) -> (r: Result<(), LinError>)
        ensures
            r is Ok <==> old(self).state == LinState::Live,
            r is Ok ==> final(self).state == LinState::Consumed,
            r is Err ==> *final(self) == *old(self),
    {
        match self.state {
            LinState::Live => {
                self.state = LinState::Consumed;
                Ok(())
            },
            _ => Err(LinError::NotLive),
        }
    }

    /// Unwinds the value. Returns true if `on abort` must run now.
    ///
    /// `on abort` runs at most once, and only for a value that is still live.
    pub fn unwind(&mut self) -> (run_on_abort: bool)
        ensures
            run_on_abort == (old(self).state == LinState::Live),
            run_on_abort ==> final(self).state == LinState::Aborted,
            !run_on_abort ==> *final(self) == *old(self),
    {
        match self.state {
            LinState::Live => {
                self.state = LinState::Aborted;
                true
            },
            _ => false,
        }
    }

    /// Returns true if the value is finished (consumed or aborted).
    pub fn is_finished(&self) -> (r: bool)
        ensures
            r == (self.state != LinState::Live),
    {
        !matches!(self.state, LinState::Live)
    }
}

/// A linear value is finished at most once: after a finish, both finish
/// operations fail or do nothing.
pub proof fn lemma_finish_once(l: Linear)
    requires
        l.state != LinState::Live,
    ensures
        l.state == LinState::Consumed || l.state == LinState::Aborted,
{
}

} // verus!

impl Default for Linear {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn once_continuation_resumes_once() {
        let mut k = Continuation::new(false);
        assert_eq!(k.resume(), Ok(()));
        assert_eq!(k.resume(), Err(ContError::AlreadyResumed));
        assert!(!k.drop_now());
    }

    #[test]
    fn multi_continuation_resumes_many_times() {
        let mut k = Continuation::new(true);
        assert_eq!(k.resume(), Ok(()));
        assert_eq!(k.resume(), Ok(()));
    }

    #[test]
    fn dropped_continuation_aborts_once() {
        let mut k = Continuation::new(false);
        assert!(k.drop_now());
        assert!(!k.drop_now());
        assert_eq!(k.resume(), Err(ContError::AlreadyDropped));
    }

    #[test]
    fn linear_value_finishes_once() {
        let mut l = Linear::new();
        assert!(!l.is_finished());
        assert_eq!(l.consume(), Ok(()));
        assert!(!l.unwind());
        assert_eq!(l.consume(), Err(LinError::NotLive));
        let mut a = Linear::default();
        assert!(a.unwind());
        assert!(!a.unwind());
        assert_eq!(a.state, LinState::Aborted);
    }
}
