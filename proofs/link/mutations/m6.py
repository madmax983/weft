# DESC: Model: `lkills` without the unstable step.
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="proofs/borrowing/src/layout.rs"
sub(d,f,"    &&& flat(p).is_prefix_of(flat(q))\n    &&& exists|j: int| flat(p).len() <= j < flat(q).len() && #[trigger] unstable(flat(q)[j])\n}","    &&& flat(p).is_prefix_of(flat(q))\n    &&& flat(p).len() < flat(q).len()\n}")
