# DESC: `unwind` also runs `on abort` for a consumed value (spec and exec).
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="crates/weft-verified/src/lifecycle.rs"
sub(d,f,"            r == Ok::<bool, LinError>(true) <==> old(self).state == LinState::Live\n                && old(self).on_abort,",
        "            r == Ok::<bool, LinError>(true) <==> old(self).state != LinState::Aborted\n                && old(self).on_abort,")
sub(d,f,"            r == Ok::<bool, LinError>(false) <==> old(self).state != LinState::Live,",
        "            r == Ok::<bool, LinError>(false) <==> (old(self).state == LinState::Aborted || (old(self).state\n                == LinState::Consumed && !old(self).on_abort)),")
sub(d,f,"            LinState::Live => Err(LinError::NoOnAbort),\n","            LinState::Consumed if self.on_abort => {\n                self.state = LinState::Aborted;\n                Ok(true)\n            },\n            LinState::Live => Err(LinError::NoOnAbort),\n")
