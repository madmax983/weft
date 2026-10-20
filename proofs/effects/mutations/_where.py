"""Reads the output of Verus on stdin. Prints the function that holds the first
location of each error, with its file. The argument is the root of the copy."""
import re
import sys

root = sys.argv[1]
names = []
want = False
for line in sys.stdin:
    if line.startswith("error"):
        want = True
        continue
    m = re.match(r"\s*--> (\S+):(\d+):\d+", line)
    if not (want and m):
        continue
    want = False
    path, num = m.group(1), int(m.group(2))
    try:
        lines = open(f"{root}/{path}").read().splitlines()
    except OSError:
        continue
    fn = "?"
    for text in reversed(lines[:num]):
        f = re.search(r"\bfn\s+(\w+)", text)
        if f:
            fn = f.group(1)
            break
    name = f"{fn} ({path.removeprefix('src/')})"
    if name not in names:
        names.append(name)
print(", ".join(names) if names else "no location")
