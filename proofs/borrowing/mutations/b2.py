# DESC: B2: `clos_survivors` keeps every closure value (no kill through captures).
import sys; sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0]); from _lib import sub
d = sys.argv[1]
sub(d, "src/model.rs",
    "Map::new(ss.clos.dom().filter(|c: CVar| !caps_killed(gs, ss.clos[c])), |c: CVar| ss.clos[c])",
    "Map::new(ss.clos.dom(), |c: CVar| ss.clos[c])")
