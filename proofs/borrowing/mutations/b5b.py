# DESC: B5: `aborts` has no `Child` case.
# EXPECT: 166 verified, 3 errors
import sys; sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0]); from _lib import sub
d = sys.argv[1]
sub(d, "src/progress.rs",
    "        Instr::Child { src, label, .. } => !dangling(s, src) && forall|idx: nat|\n            #[trigger] kid_at(s.heap, s.vars[src].addr, (label, idx)) is None,\n",
    "")
