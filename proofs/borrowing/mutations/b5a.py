# DESC: B5: `instr_ok` accepts a `Borrow` of any local.
import sys; sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0]); from _lib import sub
d = sys.argv[1]
sub(d, "src/model.rs",
    "Instr::Borrow { x, .. } => ss.locals.contains(x),",
    "Instr::Borrow { .. } => true,")
