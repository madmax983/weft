#!/usr/bin/env python3
"""Line-based reducer for Weft programs.

reduce.py IN OUT MODE ARG
  MODE 'unsound': keep programs that the checker accepts and that fault with a
                  message containing ARG (stock or instrumented).
  MODE 'fp':      keep programs that the checker rejects with code ARG and that
                  run cleanly with the instrumented interpreter on all seeds.
"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
STOCK = "/home/user/wt-edge/target/release/weft"
INST = os.path.join(HERE, "weft-inst/target/release/weft")
SEEDS = [(1, 1), (2, 4), (3, 2), (7, 4)]


def codes_of(path):
    p = subprocess.run([STOCK, "check", path], capture_output=True, text=True, timeout=60)
    out = p.stdout + p.stderr
    if "panicked" in out:
        return None
    import re
    return set(re.findall(r"error\[(W\d+)\]", out))


def run_msgs(path, binary):
    msgs = []
    for s, w in SEEDS:
        try:
            p = subprocess.run([binary, "run", path, "--unchecked", "--seed", str(s), "--workers", str(w)],
                               capture_output=True, text=True, timeout=20)
        except subprocess.TimeoutExpired:
            msgs.append("timeout")
            continue
        out = p.stdout + p.stderr
        if "runtime error:" in out:
            msgs.append(out[out.index("runtime error:"):].splitlines()[0])
        elif p.returncode != 0 and "error[" not in out:
            msgs.append("fail:" + out[-200:])
        else:
            msgs.append("ok")
    return msgs


def interesting(text, mode, arg):
    with tempfile.NamedTemporaryFile("w", suffix=".wf", dir=os.path.join(HERE, "tmp"), delete=False) as f:
        f.write(text)
        path = f.name
    try:
        codes = codes_of(path)
        if codes is None:
            return False
        if mode == "unsound":
            if codes:
                return False
            ms = run_msgs(path, STOCK) + run_msgs(path, INST)
            return any(arg in m for m in ms)
        if mode == "fp":
            if arg not in codes:
                return False
            # Other codes are fine only if they are the same kind of claim.
            ms = run_msgs(path, INST)
            return all(m == "ok" for m in ms)
        if mode == "fp1":
            if codes != {arg}:
                return False
            ms = run_msgs(path, INST)
            return all(m == "ok" for m in ms)
    finally:
        os.unlink(path)
    return False


def blocks(lines):
    """Candidate removals: (start, end) inclusive line ranges."""
    out = []
    for i, l in enumerate(lines):
        s = l.rstrip()
        opens = s.count("{") - s.count("}")
        if opens == 0 and s.strip() and not s.strip().startswith("}"):
            out.append((i, i))
        elif opens > 0:
            depth = 0
            for j in range(i, len(lines)):
                depth += lines[j].count("{") - lines[j].count("}")
                if depth == 0:
                    out.append((i, j))
                    break
    return out


def reduce(text, mode, arg):
    lines = text.splitlines()
    changed = True
    while changed:
        changed = False
        cands = blocks(lines)
        # Bigger ranges first.
        cands.sort(key=lambda r: -(r[1] - r[0]))
        for (a, b) in cands:
            if b >= len(lines):
                continue
            new = lines[:a] + lines[b + 1:]
            if interesting("\n".join(new) + "\n", mode, arg):
                lines = new
                changed = True
                break
    return "\n".join(lines) + "\n"


def main():
    src, dst, mode, arg = sys.argv[1:5]
    os.makedirs(os.path.join(HERE, "tmp"), exist_ok=True)
    text = open(src).read()
    if not interesting(text, mode, arg):
        print("not interesting at start")
        sys.exit(1)
    out = reduce(text, mode, arg)
    open(dst, "w").write(out)
    print(out)


if __name__ == "__main__":
    main()
