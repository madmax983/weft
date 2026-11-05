"""The command line of the generators (stage C2 of docs/plan/core-ir.md).

Each generator module has a function generate(seed) that gives the text of one
program, or None. The seed is the only input: the same seed gives the same
program. Run the generators with `python3 -I`.

    GEN.py SEED
        Writes the program of SEED to the standard output.
    GEN.py --seed-base B --n N --out DIR
        Writes the programs of the seeds B to B+N-1 into DIR, one file
        DIR/<name>_<seed>.wf for each seed. A seed with no program gets no file.
        Writes the number of files to the standard output.

`weft-gate sweep` uses the second form.
"""
import os
import sys


def usage(name):
    sys.stderr.write(f"usage: {name}.py SEED\n"
                     f"       {name}.py --seed-base B --n N --out DIR\n")
    sys.exit(2)


def number(name, text):
    try:
        v = int(text)
    except ValueError:
        usage(name)
    if v < 0:
        usage(name)
    return v


def main(name, generate, argv=None):
    args = sys.argv[1:] if argv is None else argv
    if len(args) == 1:
        text = generate(number(name, args[0]))
        if text is None:
            sys.exit(1)
        sys.stdout.write(text if text.endswith("\n") else text + "\n")
        return
    opts = {}
    it = iter(args)
    for a in it:
        if a not in ("--seed-base", "--n", "--out"):
            usage(name)
        v = next(it, None)
        if v is None:
            usage(name)
        opts[a] = v
    if set(opts) != {"--seed-base", "--n", "--out"}:
        usage(name)
    base = number(name, opts["--seed-base"])
    n = number(name, opts["--n"])
    out = opts["--out"]
    os.makedirs(out, exist_ok=True)
    written = 0
    for seed in range(base, base + n):
        text = generate(seed)
        if text is None:
            continue
        with open(os.path.join(out, f"{name}_{seed}.wf"), "w") as fh:
            fh.write(text if text.endswith("\n") else text + "\n")
        written += 1
    print(written)
