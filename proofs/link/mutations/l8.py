# DESC: `unwind` runs `on abort` for a type with no `on abort` (spec and exec).
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="crates/weft-verified/src/lifecycle.rs"
sub(d,f,"            r == Ok::<bool, LinError>(true) <==> old(self).state == LinState::Live\n                && old(self).on_abort,",
        "            r == Ok::<bool, LinError>(true) <==> old(self).state == LinState::Live,")
sub(d,f,"            r is Err <==> old(self).state == LinState::Live && !old(self).on_abort,","            r is Err <==> false,")
sub(d,f,"            LinState::Live if self.on_abort => {","            LinState::Live => {")
sub(d,f,"            LinState::Live => Err(LinError::NoOnAbort),\n","")
