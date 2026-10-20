# DESC: (d) allow `rets[j] <= env.len()` at `Handle`.
# EXPECT: 119 verified, 3 errors
import sys; sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0]); from _lib import sub
d = sys.argv[1]
f = "src/checker.rs"
sub(d, f, "#[trigger] prog.blocks[body].sig.rets[j]\n                    < ss.env.len()", "#[trigger] prog.blocks[body].sig.rets[j]\n                    <= ss.env.len()")
