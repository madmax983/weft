# DESC: `unwind` also runs `on abort` for a consumed value (spec and exec).
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="crates/weft-verified/src/lifecycle.rs"
sub(d,f,"            run_on_abort == (old(self).state == LinState::Live),","            run_on_abort == (old(self).state != LinState::Aborted),")
sub(d,f,"        match self.state {\n            LinState::Live => {\n                self.state = LinState::Aborted;","        match self.state {\n            LinState::Live | LinState::Consumed => {\n                self.state = LinState::Aborted;")
