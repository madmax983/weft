# DESC: `Elem` and `Seg` do not alias (spec and exec).
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="crates/weft-verified/src/places.rs"
sub(d,f,"        (StepKind::Elem, StepKind::Elem | StepKind::Seg { .. })\n        | (StepKind::Seg { .. }, StepKind::Elem)\n        | (StepKind::Deref, StepKind::Deref) => true,\n","        (StepKind::Elem, StepKind::Elem) | (StepKind::Deref, StepKind::Deref) => true,\n",count=2)
