#!/usr/bin/env python3
"""Differential soundness harness (review round 3): weft check vs. the interpreter.

Usage: harness.py OUTDIR SOURCE START COUNT
  SOURCE is a generator module name in this directory (gen3, mutate3, ...) with a
  function generate(k), or a directory of .wf files.
For each program: run the checker. Run an accepted program with
`--unchecked --oracle` under several seeds and worker counts, and with the
stock interpreter (no --oracle) when the oracle finds a fault. A fault in an
accepted program is a soundness candidate. A rejected program that runs
cleanly with the oracle on all seeds is a false-positive candidate.
"""
import json
import os
import resource
import subprocess
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
W = os.environ.get("WEFT", "/tmp/claude-0/-home-user-weft/da0e5bf6-1701-54dd-be37-5c174a731219/scratchpad/r3/target/release/weft")
RUNS = [(1, 1), (2, 4), (3, 2), (7, 4), (11, 1), (42, 3)]

BENIGN = ["out of bounds", "integer overflow", "unsigned underflow", "integer underflow", "does not fit in", "cannot listen on", "division by zero", "duration underflow",
          "split point is out of bounds"]


def check(path):
    p = subprocess.run([W, "check", "--json", path], capture_output=True, text=True, timeout=60)
    codes = []
    for line in p.stdout.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            d = json.loads(line)
        except ValueError:
            continue
        if d.get("severity") == "error":
            codes.append((d.get("code"), d.get("line")))
    crashed = p.returncode not in (0, 1) or "panicked" in p.stderr or "overflowed its stack" in p.stderr
    return codes, crashed, p.stderr[-2000:]


def limit():
    resource.setrlimit(resource.RLIMIT_AS, (3 << 30, 3 << 30))


def run(path, cmd, seed, workers, oracle):
    args = [W, cmd, path, "--unchecked", "--seed", str(seed), "--workers", str(workers)]
    if oracle:
        args.append("--oracle")
    try:
        p = subprocess.run(args, capture_output=True, text=True, timeout=10, preexec_fn=limit)
    except subprocess.TimeoutExpired:
        return ("timeout", "")
    out = p.stdout + p.stderr
    if "panicked" in out or "overflowed its stack" in out:
        return ("panic", out[-1500:])
    if "runtime error:" in out:
        msg = out[out.index("runtime error:"):].splitlines()
        loc = ""
        for l in msg[1:3]:
            if "-->" in l:
                loc = l.strip()
        m = msg[0]
        if any(b in m for b in BENIGN):
            return ("benign", m + " " + loc)
        return ("fault", m + " " + loc)
    for marker in ("<moved>", "<freed>", "<dangling>"):
        if marker in p.stdout:
            return ("fault", "printed " + marker)
    if "step limit" in out:
        return ("steplimit", out[-300:])
    if "deadlock" in out:
        return ("deadlock", out[-300:])
    if p.returncode != 0:
        return ("fail", out[-300:])
    return ("ok", "")


def one(args):
    path, cmd = args
    try:
        codes, crashed, err = check(path)
    except subprocess.TimeoutExpired:
        return {"path": path, "crash": True, "err": "check timeout", "codes": []}
    res = {"path": path, "codes": codes, "crash": crashed, "err": err if crashed else "", "cmd": cmd}
    results = []
    runs = RUNS if not codes else RUNS[:4]
    for seed, workers in runs:
        i = run(path, cmd, seed, workers, True)
        s = None
        if not codes and i[0] not in ("ok", "benign", "fail"):
            s = run(path, cmd, seed, workers, False)
        results.append((seed, workers, s, i))
        if codes and i[0] not in ("ok", "benign", "fail"):
            break   # rejected and faults: true positive, stop early
    res["runs"] = results
    return res


def classify(res):
    if res.get("crash"):
        return "CRASH"
    runs = res.get("runs", [])
    if not res["codes"]:
        for _, _, s, i in runs:
            if s and s[0] in ("fault", "panic"):
                return "UNSOUND_STOCK"
        for _, _, s, i in runs:
            if i[0] in ("fault", "panic"):
                return "UNSOUND_ORACLE"
        for _, _, s, i in runs:
            if i[0] in ("timeout", "deadlock", "steplimit"):
                return "ACCEPT_" + i[0].upper()
        return "ACCEPT_OK"
    for _, _, s, i in runs:
        if i[0] not in ("ok", "benign", "fail"):
            return "REJECT_FAULT"
    if any(i[0] != "ok" for _, _, s, i in runs):
        return "REJECT_BENIGN"
    return "REJECT_CLEAN"


def main():
    outdir, source, start, count = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    os.makedirs(outdir, exist_ok=True)
    jobs = []
    if not os.path.isdir(source):
        sys.path.insert(0, HERE)
        mod = __import__(source)
        for k in range(start, start + count):
            text = mod.generate(k)
            if text is None:
                continue
            p = os.path.join(outdir, f"p{k}.wf")
            with open(p, "w") as f:
                f.write(text)
            cmd = "test" if "\ntest \"" in text and "\nfn main(" not in text else "run"
            jobs.append((p, cmd))
    else:
        for fn in sorted(os.listdir(source)):
            if fn.endswith(".wf"):
                p = os.path.join(source, fn)
                text = open(p).read()
                cmd = "test" if "\ntest \"" in text and "fn main(" not in text else "run"
                jobs.append((p, cmd))
    with Pool(int(os.environ.get("JOBS", "4"))) as pool:
        out = pool.map(one, jobs, chunksize=4)
    summary = {}
    with open(os.path.join(outdir, "results.jsonl"), "w") as f:
        for r in out:
            c = classify(r)
            r["class"] = c
            summary[c] = summary.get(c, 0) + 1
            f.write(json.dumps(r) + "\n")
    # Keep disk use small: remove accepted-clean and rejected-fault programs.
    if os.environ.get("KEEP") != "1":
        for r in out:
            if r["class"] in ("ACCEPT_OK", "REJECT_FAULT", "REJECT_BENIGN"):
                try:
                    os.unlink(r["path"])
                except OSError:
                    pass
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
