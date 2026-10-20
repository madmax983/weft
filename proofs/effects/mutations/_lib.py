"""Helpers for the mutation patches. Each patch takes the root of a copy of the sources."""
import sys


def sub(d, f, old, new, count=1):
    """Replace `old` with `new` in file `f` of the copy `d`. `old` must occur `count` times."""
    p = d + "/" + f
    s = open(p).read()
    n = s.count(old)
    if n != count:
        print(f"patch: {f}: expected {count} match(es), found {n}: {old[:60]!r}")
        sys.exit(1)
    open(p, "w").write(s.replace(old, new))
