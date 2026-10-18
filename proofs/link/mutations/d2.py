# DESC: Spec only: `spec_closed` has no propagation rule.
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="crates/weft-verified/src/dataflow.rs"
sub(d,f,"0 <= p < kill.len() && s.contains(p) && !kill[p] && #[trigger] spec_edge(succ, p, q)\n            ==> s.contains(q)",
        "false && #[trigger] spec_edge(succ, p, q)\n            ==> s.contains(q)")
