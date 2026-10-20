# DESC: B3: `Read` needs no static type check, only `field_only(path)`.
# EXPECT: 167 verified, 2 errors
import sys; sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0]); from _lib import sub
d = sys.argv[1]
sub(d, "src/layout.rs",
    "LInstr::Read { src, path } => ss.vars.contains_key(src) && prim_at(sc, ss, ss.vars[src], path),",
    "LInstr::Read { src, path } => ss.vars.contains_key(src) && field_only(path),")
