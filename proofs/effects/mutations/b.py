# DESC: (b) `Resume` keeps a `once` continuation usable.
# EXPECT: 119 verified, 3 errors
import sys; sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0]); from _lib import sub
d = sys.argv[1]
f = "src/checker.rs"
sub(d, f, "            k: if sig.kmode == Some(Mode::Once) {\n                false\n", "            k: if sig.kmode == Some(Mode::Once) {\n                ss.k\n")
