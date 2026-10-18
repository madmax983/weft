# DESC: Model: `do_return` does not mark the dropped `once` record used.
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="proofs/effects/src/model.rs"
sub(d,f,"            pending: s.pending + s.konts[kid].frames,\n            konts: s.konts.insert(kid, Kont { used: true, ..s.konts[kid] }),",
        "            pending: s.pending + s.konts[kid].frames,\n            konts: s.konts,")
