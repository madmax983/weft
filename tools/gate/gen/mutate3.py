#!/usr/bin/env python3
"""Mutation of seed programs for review round 3.

Seeds: the interpreter programs, the corpus programs with `main` or test blocks
(with the lines that carry `//~` markers removed, so that more of them pass the
checker), and accepted generated programs in seeds3/. generate(k) picks a seed
and applies 1 to 4 line mutations: move, delete, duplicate or swap statements;
insert a push, clear, pop, move, rebind or borrow of a local; wrap a statement in
a block, a loop, a closure, `twice`, a handler, a scope, a task, a `fork`,
`with_timeout`; turn a statement into a tail place; swap `once` and `multi`;
add or remove a `resume`; remove a consumer or an `on abort`; remove a handler;
detach a task; move a join.
"""
import glob
import os
import random
import re

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = "/tmp/claude-0/-home-user-weft/da0e5bf6-1701-54dd-be37-5c174a731219/scratchpad/r3/src"
EXTRA = """
fn twice_m(f: fn()) { f(); f() }
fn apply_m(f: fn()) { f() }
fn spawn_m(f: fn()) { scope { s => s.spawn(f) } }
fn take_m<T>(x: T) { }
"""


def seeds():
    out = sorted(glob.glob(SRC + "/crates/weft-interp/tests/programs/*.wf"))
    for f in sorted(glob.glob(SRC + "/tests/programs/*.wf")):
        t = open(f).read()
        if re.search(r"^(fn main|test \")", t, re.M):
            out.append(f)
    out += sorted(glob.glob(os.path.join(HERE, "seeds3/*.wf")))
    return out


SEEDS = seeds()
LET = re.compile(r"^\s*let\s+([a-z_][a-z0-9_]*)\s*(:[^=]*)?=")


def stmt_lines(lines):
    out = []
    depth = 0
    for i, l in enumerate(lines):
        s = l.strip()
        if depth >= 1 and s and not s.startswith("//") and l.count("{") == l.count("}") \
                and l.count("(") == l.count(")") \
                and not s.startswith("}") and not s.startswith("fn ") and not s.startswith("on ") \
                and "=>" not in s and not s.endswith(",") and not s.startswith("else") \
                and not s.startswith("in ") and not s.startswith("pub ") and not s.startswith("multi"):
            out.append(i)
        depth += l.count("{") - l.count("}")
    return out


def names_before(lines, i):
    names = []
    for j in range(i, -1, -1):
        if re.match(r"^(pub )?(fn |test )", lines[j]):
            break
        m = LET.match(lines[j])
        if m and m.group(1) != "_":
            names.append(m.group(1))
    return names


def indent(l):
    return l[:len(l) - len(l.lstrip())]


def mutate_once(r, lines):
    st = stmt_lines(lines)
    if not st:
        return lines
    op = r.choice(["move", "move", "delete", "dup", "swap", "insert", "insert", "insert", "insert", "wrap", "wrap",
                   "wrap", "wrap", "multi", "resume", "noconsume", "nohandle", "detach", "rebind", "tail", "join",
                   "borrow_use"])
    i = r.choice(st)
    ind = indent(lines[i])
    if op == "move":
        same = [j for j in st if indent(lines[j]) == ind and j != i and abs(j - i) <= 4]
        if same:
            j = r.choice(same)
            l = lines.pop(i)
            lines.insert(j, l)
    elif op == "delete":
        lines.pop(i)
    elif op == "dup":
        lines.insert(i, lines[i])
    elif op == "swap":
        if i + 1 < len(lines) and i + 1 in st and indent(lines[i + 1]) == ind:
            lines[i], lines[i + 1] = lines[i + 1], lines[i]
    elif op == "insert":
        ns = names_before(lines, i)
        if ns:
            x = r.choice(ns)
            y = r.choice(ns)
            snip = r.choice([f"{x}.push({x}[0])", f"{x}.clear()", f"let _ = {x}.pop()", f"let m_{x} = {x}",
                             f"print({x})", f"{x} = {y}", f"let r_{x} = &{x}", f"print({x}.len())",
                             f"{x}.push(1)", f"let q_{x} = &{x}[0]", f"apply_m(|| print({x}))",
                             f"twice_m(|| {x}.clear())", f"let g_{x} = || {x}.clear()", f"take_m({x})",
                             f"let g_{x} = || take_m({x})", f"spawn_m(|| print({x}))", f"{{ {x} }}; print(0)",
                             f"let h_{x} = Some({x})", f"let b_{x} = Box.new({x})"])
            lines.insert(i + r.choice([0, 1]), ind + snip)
    elif op == "borrow_use":
        ns = names_before(lines, i)
        if ns:
            x = r.choice(ns)
            lines.insert(i, ind + f"let bq_{x} = &{x}")
            k = r.choice([j for j in st if j > i] or [i])
            if k < len(lines) - 1:
                lines.insert(k + 1, indent(lines[k]) + f"print(bq_{x})")
    elif op == "wrap":
        s = lines[i].strip()
        if s.startswith("let ") or s.startswith("return") or s.startswith("break") or s.startswith("continue"):
            return lines
        w = r.choice([f"{{ {s} }}", f"for i_w in 0..2 {{ {s} }}", f"if true {{ {s} }}",
                      f"let g_w = || {{ {s} }}; g_w()", f"twice_m(|| {{ {s} }})", f"apply_m(|| {{ {s} }})",
                      f"scope {{ s_w => s_w.spawn(|| {{ {s} }}) }}",
                      f"scope {{ s_w => let t_w = s_w.spawn(|| {{ {s} }}); t_w.join() }}",
                      f"spawn_m(|| {{ {s} }})",
                      f"handle Fail {{ fn fail(m) {{ print(m) }} }} in {{ {s} }}",
                      f"let _ = fork(|| {{ {s} }}, || print(0))",
                      f"loop {{ {s}; break }}", f"with_timeout(9.s) {{ {s} }}",
                      f"scope {{ s_w => {s} }}"])
        lines[i] = ind + w
    elif op == "tail":
        ns = names_before(lines, i)
        if ns:
            x = r.choice(ns)
            lines.insert(i + 1, ind + r.choice([f"{{ {x} }}", f"if true {{ {x} }}", f"{x}", f"let _ = {x}"]))
    elif op == "multi":
        cands = [j for j, l in enumerate(lines) if re.search(r"^\s*(multi )?fn \w+\(", l) and
                 any(lines[k].startswith("effect ") for k in range(max(0, j - 6), j + 1))]
        cands += [j for j, l in enumerate(lines) if l.startswith("effect ") and "fn " in l]
        if cands:
            j = r.choice(cands)
            if "multi fn" in lines[j]:
                lines[j] = lines[j].replace("multi fn", "fn", 1)
            else:
                lines[j] = re.sub(r"\bfn\s", "multi fn ", lines[j], count=1)
    elif op == "resume":
        cands = [j for j, l in enumerate(lines) if "resume(" in l]
        if cands:
            j = r.choice(cands)
            if r.random() < 0.5:
                lines[j] = re.sub(r"resume\(([^()]*)\)", r"resume(\1); resume(\1)", lines[j], count=1)
            else:
                lines[j] = re.sub(r"resume\(([^()]*)\)", r"print(0)", lines[j], count=1)
    elif op == "noconsume":
        cands = [j for j in st if re.search(r"\b(commit|unlock|rollback|close|finish|join|consume|done)\(", lines[j])
                 or re.search(r"let [A-Z]\w*\(", lines[j])]
        if cands:
            lines.pop(r.choice(cands))
        else:
            ab = [j for j, l in enumerate(lines) if l.strip().startswith("on abort")]
            if ab:
                lines.pop(r.choice(ab))
    elif op == "nohandle":
        cands = [j for j, l in enumerate(lines) if re.search(r"handle \w+ \{.*\} in ", l)]
        if cands:
            j = r.choice(cands)
            lines[j] = re.sub(r"handle \w+ \{.*?\} *\} in ", "", lines[j], count=1)
    elif op == "detach":
        cands = [j for j, l in enumerate(lines) if ".join()" in l]
        if cands:
            j = r.choice(cands)
            lines[j] = lines[j].replace(".join()", ".detach()", 1)
    elif op == "join":
        cands = [j for j, l in enumerate(lines) if re.match(r"^\s*\w+\.join\(\)\s*$", l)]
        if cands:
            j = r.choice(cands)
            l = lines.pop(j)
            k = max(0, min(len(lines) - 1, j + r.choice([-3, -2, -1, 1, 2, 3])))
            if k in stmt_lines(lines):
                lines.insert(k, indent(lines[k]) + l.strip())
            else:
                lines.insert(j, l)
    elif op == "rebind":
        ns = names_before(lines, i)
        if len(ns) >= 2:
            a, b = r.sample(ns, 2)
            lines.insert(i + 1, ind + f"{a} = {b}")
    return lines


def generate(k):
    r = random.Random(k * 7919 + 17)
    if not SEEDS:
        return None
    src = open(SEEDS[k % len(SEEDS)]).read()
    lines = [l for l in src.splitlines() if "//~" not in l or r.random() < 0.15]
    for _ in range(r.randint(1, 4)):
        lines = mutate_once(r, lines)
    return "\n".join(lines) + "\n" + EXTRA


if __name__ == "__main__":
    import sys
    print(generate(int(sys.argv[1])))
