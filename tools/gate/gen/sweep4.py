#!/usr/bin/env python3
"""Sweep 4: a task and its parent touch one variable while the task runs.

`sweep4.py --all OUTDIR` writes one program for each way to start the task,
each access of the task, each access of the parent and each frame around the
parent access (the round-3 sweep). The task is joined after the parent access
(at the end of the scope).

generate(seed) gives one random program of a larger set: one or two accesses
of the task, one or two accesses of the parent, each in its own frame, and a
join before, between or after the accesses of the parent (stage C2). The other
command lines are those of genmain.py.
"""
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

PRE = r'''effect Note { fn note(x: u64) }
struct Two { a: Vec<u64>, b: Vec<u64>, n: u64 }
fn mk_v() -> Vec<u64> { let v = Vec.new(); v.push(1); v.push(2); v }
fn mk_t() -> Two { Two { a: mk_v(), b: mk_v(), n: 0 } }
fn grow(v: &Vec<u64>) { v.push(9) }
fn look(v: &Vec<u64>) -> usize { v.len() }
fn take_v(v: Vec<u64>) -> usize { v.len() }
fn apply(f: fn()) { f() }
fn bump(t: &Two) { t.n += 1 }
fn id<T>(x: T) -> T { x }
impl Two {
    fn add(self, x: u64) { self.a.push(x) }
    fn size(self) -> usize { self.a.len() }
}
'''

TASK_ACC = {
    'push': 'p.a.push(1)',
    'read': 'print(p.a.len())',
    'elem_w': 'p.a[0] = 3',
    'elem_r': 'print(p.a[0])',
    'grow': 'grow(&p.a)',
    'method_w': 'p.add(4)',
    'scalar_w': 'p.n += 1',
    'whole_r': 'print(p.n + p.a.len())',
    'bump': 'bump(&p)',
    'rebind': 'p.a = mk_v()',
}
PARENT_ACC = {
    'push': 'p.a.push(5)',
    'read': 'print(p.a.len())',
    'elem_r': 'print(p.a[1])',
    'borrow': 'let q = &p.a[0]; print(q + 0)',
    'borrow_whole': 'let q = &p.a; print(q.len())',
    'look': 'print(look(&p.a))',
    'method_r': 'print(p.size())',
    'scalar_r': 'print(p.n)',
    'move_part': 'print(take_v(p.a))',
    'rebind_part': 'p.a = mk_v()',
    'whole_print': 'print(p.n + 1)',
    'id': 'let q = id(&p.a); print(q.len())',
    'other': 'print(p.b.len())',
}
FRAMES = {
    'plain': '{A}',
    'block': '{{ {A} }}',
    'closure': 'let g = || {{ {A} }}; g()',
    'apply': 'apply(|| {{ {A} }})',
    'handle': 'handle Note {{ fn note(x) {{ resume(()) }} }} in {{ note(1); {A} }}',
    'clause': 'handle Note {{ fn note(x) {{ {A}; resume(()) }} }} in {{ note(1) }}',
    'if': 'if 1 < 2 {{ {A} }}',
    'for': 'for i in 0..1 {{ {A} }}',
    'inner_task': 'scope {{ s2 => let t2 = s2.spawn(|| {{ {A} }}); t2.join() }}',
}
STARTS = {
    'spawn': 's.spawn(|| {{ {T} }})',
    'spawn_let': 'let t = s.spawn(|| {{ {T} }})',
    'spawn_clo': 'let mk = || s.spawn(|| {{ {T} }}); mk()',
    'spawn_clause': 'handle Note {{ fn note(x) {{ s.spawn(|| {{ {T} }}); resume(()) }} }} in {{ note(1) }}',
    'spawn_fnval': 'let w = || {{ {T} }}; s.spawn(w)',
}


def generate(seed):
    """One random program for `seed`."""
    r = random.Random(seed)
    sn = r.choice(sorted(STARTS))
    tas = [TASK_ACC[k] for k in r.sample(sorted(TASK_ACC), r.choice([1, 1, 2]))]
    task = "; ".join(tas)
    accs = []
    for _ in range(r.choice([1, 1, 2])):
        pa = PARENT_ACC[r.choice(sorted(PARENT_ACC))]
        accs.append(FRAMES[r.choice(sorted(FRAMES))].format(A=pa))
    lines = ["fn main() {", "    let p = mk_t()", "    scope { s =>", "        " + STARTS[sn].format(T=task)]
    join = r.randrange(len(accs) + 1) if sn == 'spawn_let' else None
    for i, acc in enumerate(accs):
        if join == i:
            lines.append("        t.join()")
        lines.append("        " + acc)
    if join == len(accs):
        lines.append("        t.join()")
    lines += ["    }", "    print(p.n)", "}"]
    return PRE + "\n" + "\n".join(lines) + "\n"


def enumerate_all(out):
    os.makedirs(out, exist_ok=True)
    n = 0
    for sn, st in STARTS.items():
        for tn, ta in TASK_ACC.items():
            for pn, pa in PARENT_ACC.items():
                for fn, ft in FRAMES.items():
                    if fn not in ('plain', 'closure', 'handle', 'clause', 'inner_task') and sn != 'spawn_let':
                        continue
                    start = st.format(T=ta)
                    acc = ft.format(A=pa)
                    lines = ["fn main() {", "    let p = mk_t()", "    scope { s =>",
                             "        " + start, "        " + acc]
                    if sn == 'spawn_let':
                        lines.append("        t.join()")
                    lines += ["    }", "    print(p.n)", "}"]
                    text = PRE + "\n" + "\n".join(lines) + "\n"
                    with open(os.path.join(out, f"{sn}__{tn}__{pn}__{fn}.wf"), "w") as fh:
                        fh.write(text)
                    n += 1
    print(n)


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--all":
        enumerate_all(sys.argv[2])
    else:
        import genmain
        genmain.main("sweep4", generate)
