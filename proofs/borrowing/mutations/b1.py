# DESC: B1: `cfg_check` checks only forward edges, so back edges do not join.
import sys; sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0]); from _lib import sub
d = sys.argv[1]
sub(d, "src/cfg.rs",
    "#[trigger] cfg[n].succs[j] < cfg.len()\n            && sub_state(ann[cfg[n].succs[j] as int], post(ann[n], cfg[n].instr))",
    "#[trigger] cfg[n].succs[j] < cfg.len()\n            && (cfg[n].succs[j] > n ==> sub_state(ann[cfg[n].succs[j] as int], post(ann[n], cfg[n].instr)))")
