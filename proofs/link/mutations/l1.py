# DESC: A dropped `multi` continuation can resume (spec and exec).
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="crates/weft-verified/src/lifecycle.rs"
sub(d,f,"            old(self).state == ContState::Dropped ==> r == Err::<(), ContError>(",
        "            old(self).state == ContState::Dropped && !old(self).multi ==> r == Err::<(), ContError>(")
sub(d,f,"            r is Ok <==> (old(self).state == ContState::Fresh || (old(self).state\n                == ContState::Resumed && old(self).multi)),",
        "            r is Ok <==> (old(self).state == ContState::Fresh || (old(self).state\n                != ContState::Fresh && old(self).multi)),")
sub(d,f,"            ContState::Dropped => Err(ContError::AlreadyDropped),","            ContState::Dropped if !self.multi => Err(ContError::AlreadyDropped),")
