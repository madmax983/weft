# DESC: Model: only `Kid` steps are unstable.
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="proofs/borrowing/src/layout.rs"
sub(d,f,"pub open spec fn unstable(st: PStep) -> bool {\n    !(st is Field)\n}","pub open spec fn unstable(st: PStep) -> bool {\n    st is Kid\n}")
