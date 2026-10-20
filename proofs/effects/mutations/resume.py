# DESC: drop the suspension rule at `Resume`.
# EXPECT: 121 verified, 1 error
import sys; sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0]); from _lib import sub
d = sys.argv[1]
f = "src/checker.rs"
sub(d, f, "            &&& sig.kmode is Some\n            &&& susp_ok(prog, sig, post(prog, sig, ss, i), ss.env)\n", "            &&& sig.kmode is Some\n")
