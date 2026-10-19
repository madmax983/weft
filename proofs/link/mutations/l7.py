# DESC: `drop_now` makes an aborted record `once` (spec and exec).
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="crates/weft-verified/src/lifecycle.rs"
sub(d,f,"            final(self).multi == old(self).multi,\n            aborts == (old(self).state == ContState::Fresh),",
        "            aborts ==> !final(self).multi,\n            aborts == (old(self).state == ContState::Fresh),")
sub(d,f,"            ContState::Fresh => {\n                self.state = ContState::Dropped;",
        "            ContState::Fresh => {\n                self.state = ContState::Dropped;\n                self.multi = false;")
