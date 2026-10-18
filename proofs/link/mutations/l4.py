# DESC: Model: a used `once` continuation can resume.
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="proofs/effects/src/model.rs"
sub(d,f,"    f.k is Some && s.konts.contains_key(f.k->0) && (s.konts[f.k->0].multi || !s.konts[f.k->0].used)\n}",
        "    f.k is Some && s.konts.contains_key(f.k->0)\n}")
