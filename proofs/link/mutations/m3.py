# DESC: `Elem` and `Seg` do not alias (spec and exec).
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="crates/weft-verified/src/places.rs"
sub(d,f,"        (StepKind::Elem, StepKind::Seg { .. }) => true,\n        (StepKind::Seg { .. }, StepKind::Elem) => true,\n","        (StepKind::Elem, StepKind::Seg { .. }) => false,\n        (StepKind::Seg { .. }, StepKind::Elem) => false,\n",count=2)
