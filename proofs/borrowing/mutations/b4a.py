# DESC: B4: `overlap` in one direction only.
import sys; sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0]); from _lib import sub
d = sys.argv[1]
sub(d, "src/tasks.rs",
    "a.root == b.root && (a.path.is_prefix_of(b.path) || b.path.is_prefix_of(a.path))",
    "a.root == b.root && a.path.is_prefix_of(b.path)")
