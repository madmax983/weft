//! Verified state machines for one-shot continuations and linear values.
//!
//! The interpreter uses these types at run time. The proofs show that a `once`
//! continuation resumes at most once, and that a linear value is consumed or
//! aborted at most once. They do not show that each linear value is finished:
//! the static checker (W0601, W0602) and the unwinder of the interpreter must
//! do that.
//!
//! `proofs/link` includes this file (`proofs/link/src/lifecycle_link.rs`). It
//! proves that each operation is a step of the continuation and resource
//! records of the effects model, and that each operation fails where the
//! model step is an error. Two differences are about `multi` continuations:
//! `drop_now` aborts a fresh `multi` continuation, and a resume after that
//! abort fails. The model does not abort it, and it allows the resume.
//! `proofs/verify-all.sh` runs the link. Run `proofs/link/verify.sh` after a
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
    pub const fn new(multi: bool) -> (r: Self)
        ensures
            r.state == ContState::Fresh,
            r.multi == multi,
    {
        Self { state: ContState::Fresh, multi }
    }

    /// Records a resume. A `once` continuation accepts only one resume.
    pub const fn resume(&mut self) -> (r: Result<(), ContError>)
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
    /// continuation was never resumed. The mode does not change.
    pub const fn drop_now(&mut self) -> (aborts: bool)
        ensures
            final(self).multi == old(self).multi,
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
    /// True if the type of the value has `on abort`.
    pub on_abort: bool,
}

/// Why a linear operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LinError {
    /// The value is already consumed or aborted.
    NotLive,
    /// The unwinder found a live value, and its type has no `on abort`. Thus
    /// the unwinder cannot finish the value.
    NoOnAbort,
}

impl Linear {
    /// Makes a live linear value. `on_abort` tells if its type has `on abort`.
    pub const fn new(on_abort: bool) -> (r: Self)
        ensures
            r.state == LinState::Live,
            r.on_abort == on_abort,
    {
        Self { state: LinState::Live, on_abort }
    }

    /// Consumes the value on the normal path.
    pub const fn consume(&mut self) -> (r: Result<(), LinError>)
        ensures
            final(self).on_abort == old(self).on_abort,
            r is Ok <==> old(self).state == LinState::Live,
            r is Ok ==> final(self).state == LinState::Consumed,
            r is Err ==> r == Err::<(), LinError>(LinError::NotLive) && *final(self) == *old(self),
    {
        match self.state {
            LinState::Live => {
                self.state = LinState::Consumed;
                Ok(())
            },
            _ => Err(LinError::NotLive),
        }
    }

    /// Unwinds the value. Returns `Ok(true)` if `on abort` must run now, and
    /// `Ok(false)` if the value is already finished.
    ///
    /// `on abort` runs at most once, and only for a value that is still live.
    /// A live value with no `on abort` gives [`LinError::NoOnAbort`].
    pub const fn unwind(&mut self) -> (r: Result<bool, LinError>)
        ensures
            final(self).on_abort == old(self).on_abort,
            r == Ok::<bool, LinError>(true) <==> old(self).state == LinState::Live
                && old(self).on_abort,
            r == Ok::<bool, LinError>(true) ==> final(self).state == LinState::Aborted,
            r == Ok::<bool, LinError>(false) <==> old(self).state != LinState::Live,
            r is Err <==> old(self).state == LinState::Live && !old(self).on_abort,
            r is Err ==> r == Err::<bool, LinError>(LinError::NoOnAbort),
            r != Ok::<bool, LinError>(true) ==> *final(self) == *old(self),
    {
        match self.state {
            LinState::Live if self.on_abort => {
                self.state = LinState::Aborted;
                Ok(true)
            },
            LinState::Live => Err(LinError::NoOnAbort),
            _ => Ok(false),
        }
    }

    /// Returns true if the value is finished (consumed or aborted).
    pub const fn is_finished(&self) -> (r: bool)
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
        let mut l = Linear::new(true);
        assert!(!l.is_finished());
        assert_eq!(l.consume(), Ok(()));
        assert_eq!(l.unwind(), Ok(false));
        assert_eq!(l.consume(), Err(LinError::NotLive));
        let mut a = Linear::new(true);
        assert_eq!(a.unwind(), Ok(true));
        assert_eq!(a.unwind(), Ok(false));
        assert_eq!(a.state, LinState::Aborted);
        assert_eq!(a.consume(), Err(LinError::NotLive));
    }

    #[test]
    fn linear_value_with_no_on_abort_does_not_unwind() {
        let mut l = Linear::new(false);
        assert_eq!(l.unwind(), Err(LinError::NoOnAbort));
        assert_eq!(l.state, LinState::Live);
        assert_eq!(l.consume(), Ok(()));
        assert_eq!(l.unwind(), Ok(false));
    }

    #[test]
    fn drop_keeps_the_mode() {
        for multi in [false, true] {
            let mut k = Continuation::new(multi);
            assert!(k.drop_now());
            assert_eq!(k.multi, multi);
            assert_eq!(k.state, ContState::Dropped);
        }
    }
}
