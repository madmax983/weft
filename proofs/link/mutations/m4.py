# DESC: `Deref` does not alias `Deref` (spec and exec).
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="crates/weft-verified/src/places.rs"
sub(d,f,"        (StepKind::Deref, StepKind::Deref) => true,\n        _ => false,\n    }\n}\n\n/// Step `a` names","        (StepKind::Deref, StepKind::Deref) => false,\n        _ => false,\n    }\n}\n\n/// Step `a` names")
sub(d,f,"        (StepKind::Deref, StepKind::Deref) => true,\n        _ => false,\n    }\n}\n\n/// Returns true if step `a` names","        (StepKind::Deref, StepKind::Deref) => false,\n        _ => false,\n    }\n}\n\n/// Returns true if step `a` names")
