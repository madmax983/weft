# DESC: (c) drop the abort rule at a `once` perform.
# EXPECT: 120 verified, 2 errors
import sys; sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0]); from _lib import sub
d = sys.argv[1]
f = "src/checker.rs"
sub(d, f, "            &&& prog.effs[ss.env[cap as int]][op as int] == Mode::Once ==> all_abortable(ss)\n", "")
