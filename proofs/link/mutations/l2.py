# DESC: `consume` accepts an `Aborted` value (spec and exec).
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="crates/weft-verified/src/lifecycle.rs"
sub(d,f,"            r is Ok <==> old(self).state == LinState::Live,","            r is Ok <==> (old(self).state == LinState::Live || old(self).state == LinState::Aborted),")
sub(d,f,"        match self.state {\n            LinState::Live => {\n                self.state = LinState::Consumed;","        match self.state {\n            LinState::Live | LinState::Aborted => {\n                self.state = LinState::Consumed;")
