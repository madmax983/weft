# DESC: Model: `strict_child` also holds for the group itself.
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="proofs/borrowing/src/model.rs"
sub(d,f,"    g.root == p.root && p.path.len() < g.path.len() && g.path.subrange(0, p.path.len() as int)\n","    g.root == p.root && p.path.len() <= g.path.len() && g.path.subrange(0, p.path.len() as int)\n")
