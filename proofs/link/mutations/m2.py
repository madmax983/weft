# DESC: Rule 3 needs two steps after `m` (spec and exec).
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="crates/weft-verified/src/places.rs"
sub(d,f,"m.len() < p.len() && spec_may_prefix(m, p) && spec_crosses_unstable(m.len() as int, p)\n}","m.len() + 1 < p.len() && spec_may_prefix(m, p) && spec_crosses_unstable(m.len() as int + 1, p)\n}")
sub(d,f,"m.len() < p.len() && may_prefix(m, p) && crosses_unstable(m.len(), p)\n}","m.len() + 1 < p.len() && may_prefix(m, p) && crosses_unstable(m.len() + 1, p)\n}")
