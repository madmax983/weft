# DESC: (c) `Return` without the check that no linear value is live.
# EXPECT: 120 verified, 2 errors
import sys; sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0]); from _lib import sub
d = sys.argv[1]
f = "src/checker.rs"
sub(d, f, "        Instr::Return => forall|sl: Slot| !#[trigger] ss.lin.contains_key(sl),", "        Instr::Return => true,")
