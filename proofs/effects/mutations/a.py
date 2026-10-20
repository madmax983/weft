# DESC: (a) drop `cap < env.len()` at `Perform`.
import sys; sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0]); from _lib import sub
d = sys.argv[1]
f = "src/checker.rs"
sub(d, f, "            &&& cap < ss.env.len()\n", "")
