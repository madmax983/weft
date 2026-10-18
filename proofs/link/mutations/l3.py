# DESC: `drop_now` does not abort a fresh `multi` continuation (spec and exec).
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="crates/weft-verified/src/lifecycle.rs"
sub(d,f,"            aborts == (old(self).state == ContState::Fresh),","            aborts == (old(self).state == ContState::Fresh && !old(self).multi),")
sub(d,f,"        match self.state {\n            ContState::Fresh => {\n                self.state = ContState::Dropped;","        match self.state {\n            ContState::Fresh if !self.multi => {\n                self.state = ContState::Dropped;")
