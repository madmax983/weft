# DESC: The same side of one split does not alias itself (spec and exec).
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="crates/weft-verified/src/places.rs"
sub(d,f,"(StepKind::Seg { split: s1, hi: h1 }, StepKind::Seg { split: s2, hi: h2 }) => s1 != s2 || h1\n            == h2,","(StepKind::Seg { split: s1, hi: h1 }, StepKind::Seg { split: s2, hi: h2 }) => s1 != s2,",count=2)
