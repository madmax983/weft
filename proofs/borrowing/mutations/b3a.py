# DESC: B3: `Variant` steps are stable (only `Kid` steps are unstable).
# EXPECT: 167 verified, 2 errors
import sys; sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0]); from _lib import sub
d = sys.argv[1]
sub(d, "src/layout.rs",
    "pub open spec fn unstable(st: PStep) -> bool {\n    !(st is Field)\n}",
    "pub open spec fn unstable(st: PStep) -> bool {\n    st is Kid\n}")
