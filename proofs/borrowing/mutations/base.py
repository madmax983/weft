# DESC: Base: `strict_child` holds only for grandchild groups.
import sys; sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0]); from _lib import sub
d = sys.argv[1]
sub(d, "src/model.rs",
    "g.root == p.root && p.path.len() < g.path.len() && g.path.subrange(0, p.path.len() as int)",
    "g.root == p.root && p.path.len() + 1 < g.path.len() && g.path.subrange(0, p.path.len() as int)")
