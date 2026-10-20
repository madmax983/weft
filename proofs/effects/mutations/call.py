# DESC: drop the suspension rule at `Call`.
# EXPECT: 121 verified, 1 error
import sys; sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0]); from _lib import sub
d = sys.argv[1]
f = "src/checker.rs"
sub(d, f, "            &&& susp_ok(prog, sig, post(prog, sig, ss, i), prog.blocks[block].sig.caps)\n", "")
