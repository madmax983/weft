# DESC: `propagate` and `spec_edge` follow only the first successor (spec and exec).
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="crates/weft-verified/src/dataflow.rs"
sub(d,f,"0 <= p < succ.len() && exists|j: int| 0 <= j < succ[p].len() && succ[p][j] as int == q",
        "0 <= p < succ.len() && exists|j: int| 0 <= j < succ[p].len() && j < 1 && succ[p][j] as int == q")
sub(d,f,"    forall|j: int| 0 <= j < succ[p].len() ==> out[#[trigger] succ[p][j] as int]",
        "    forall|j: int| 0 <= j < succ[p].len() && j < 1 ==> out[#[trigger] succ[p][j] as int]")
sub(d,f,"while j < row.len()\n","while j < row.len() && j < 1\n",count=2)
# lemma_step_sound: only for the first successor
sub(d,f,"        0 <= j < succ[p].len(),\n        gen[p] || (!kill[p] && spec_in_lfp(succ, gen, kill, p)),",
        "        0 <= j < succ[p].len(),\n        j < 1,\n        gen[p] || (!kill[p] && spec_in_lfp(succ, gen, kill, p)),")
sub(d,f,"        assert forall|j: int| 0 <= j < succ[x].len() implies new_out[#[trigger] succ[x][j]\n            as int] by {",
        "        assert forall|j: int| 0 <= j < succ[x].len() && j < 1 implies new_out[#[trigger] succ[x][j]\n            as int] by {")
