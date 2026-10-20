# DESC: drop the multi rule at a `multi` perform.
import sys; sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0]); from _lib import sub
d = sys.argv[1]
f = "src/checker.rs"
sub(d, f, "            &&& prog.effs[ss.env[cap as int]][op as int] == Mode::Multi ==> all_many(sig, ss)\n", "")
