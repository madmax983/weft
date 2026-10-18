# DESC: Model: the B1 `killed` also kills through shared arguments.
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="proofs/borrowing/src/model.rs"
sub(d,f,"    exists|k: int| 0 <= k < gs.len() && gs[k].1 && #[trigger] strict_child(g, gs[k].0)\n","    exists|k: int| 0 <= k < gs.len() && #[trigger] strict_child(g, gs[k].0)\n")
