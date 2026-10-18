# DESC: Field steps alias without equal ids (spec and exec).
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="crates/weft-verified/src/places.rs"
s=open(d+"/"+f).read()
old="(StepKind::Field { id: x }, StepKind::Field { id: y }) => x == y,\n        (StepKind::Variant { id: x }, StepKind::Variant { id: y }) => x == y,\n        (StepKind::Elem, StepKind::Elem) => true,\n        (StepKind::Elem, StepKind::Seg"
new="(StepKind::Field { .. }, StepKind::Field { .. }) => true,\n        (StepKind::Variant { id: x }, StepKind::Variant { id: y }) => x == y,\n        (StepKind::Elem, StepKind::Elem) => true,\n        (StepKind::Elem, StepKind::Seg"
sub(d,f,old,new,count=2)
