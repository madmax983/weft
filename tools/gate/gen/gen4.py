#!/usr/bin/env python3
"""Generator 4 (review round 3, lens oracle): one-place call results,
loop-carried references, and task handles.

Episodes:
- inst: a call result with no stated place (`find_n`, `kid_of`, `pick_opt`)
  is one place. References into it and writes through it, through a copy, a
  second result, the base, closures, handlers and tasks.
- loopref: references that loops pass from one iteration to the next, with
  rotations, conditional new values and mutations between.
- taskh: task handles in locals, tuples, options and branches; joins in
  different places; the parent touches what the task touches.
Each episode reuses the wrappers of gen3.
"""
import os
import random

import gen3

HERE = os.path.dirname(os.path.abspath(__file__))
PRE = open(os.path.join(HERE, "lib/pre3.wf")).read() + open(os.path.join(HERE, "lib/pre4_extra.wf")).read()


class G4(gen3.G):
    def inst_ref(self, e):
        """A reference into the instance `e` (a &N): (lines, use expr)."""
        r = self.r
        k = self.fresh('k')
        return r.choice([
            ([f"let {k} = &{e}.kids[0]"], f"{k}"),
            ([f"let {k} = {e}.kids.get(1)"], f"{k}"),
            ([f"let {k} = &{e}.hp"], f"{k}"),
            ([f"let {k} = &{e}.b.hp"], f"{k}"),
            ([f"let {k} = &{e}.b"], f"{k}.hp"),
            ([f"let {k} = &{e}.kids"], f"{k}[0]"),
            ([f"let {k} = &{e}.kids"], f"{k}.len()"),
            ([f"let {k} = match kid_of({e}) {{ Some(q) => q, None => &{e}.hp }}"], f"{k}"),
            ([f"let {k} = {e}"], f"{k}.hp"),
            ([f"let {k} = {e}"], f"{k}.kids[0]"),
            ([f"let {k} = id({e})"], f"{k}.kids[1]"),
            ([f"let {k} = || {e}.kids[0]"], f"{k}()"),
            ([f"let {k} = (&{e}.kids[0], 1)"], f"{k}.0"),
        ])

    def inst_write(self, e, g, other):
        """A write that can hit what a reference into `e` points to (or not)."""
        r = self.r
        opts = [f"{e}.hp += 1", f"{e}.kids.push(3)", f"{e}.kids.clear()", f"let _ = {e}.kids.pop()",
                f"{e}.kids[0] = 9", f"{e}.b = Box.new(mk_e(4))", f"{e}.b.hp += 1", f"grow_kids({e})",
                f"grow(&{e}.kids)", f"bump_n(&{e}.hp)", f"{e}.kids = mk_v()",
                f"{g}.ns[0].kids.clear()", f"{g}.ns[1].kids.push(1)", f"{g}.ns.push(mk_n(5))", f"{g}.tot += 1",
                f"{g}.ns[0].hp += 1", f"{g}.ns[0].b = Box.new(mk_e(6))",
                f"match find_n(&{g}, 0) {{ Some(f) => f.kids.clear(), None => {{}} }}",
                f"match find_n(&{g}, 1) {{ Some(f) => f.hp += 1, None => {{}} }}",
                f"match find_n(&{g}, 0) {{ Some(f) => f.b = Box.new(mk_e(1)), None => {{}} }}",
                f"let z{self.n} = first_n(&{g})\nz{self.n}.kids.push(2)",
                f"{other}.ns[0].kids.clear()"]
        self.n += 1
        w = r.choice(opts)
        lines = w.split("\n")
        chan = r.choice(['direct', 'direct', 'direct', 'clo', 'apply', 'twice', 'handler', 'task_join', 'ifelse',
                         'copy'])
        if chan == 'direct':
            return lines
        if chan == 'clo':
            h = self.fresh('h')
            return [f"let {h} = || {{"] + ["    " + l for l in lines] + ["}", f"{h}()"]
        if chan == 'apply':
            return ["apply(|| {"] + ["    " + l for l in lines] + ["})"]
        if chan == 'twice':
            return ["twice(|| {"] + ["    " + l for l in lines] + ["})"]
        if chan == 'handler':
            return ["handle Note { fn note(x) {"] + ["    " + l for l in lines] + ["    resume(())", "} } in {", "    note(1)", "}"]
        if chan == 'task_join':
            s = self.fresh('s')
            return [f"scope {{ {s} =>", f"    let t{s} = {s}.spawn(|| {{"] + ["        " + l for l in lines] + ["    })", f"    t{s}.join()", "}"]
        if chan == 'ifelse':
            return ["if 1 < 2 {"] + ["    " + l for l in lines] + ["} else {", "    print(0)", "}"]
        if chan == 'copy':
            c = self.fresh('c')
            return [f"let {c} = {e}"] + [l.replace(f"{e}.", f"{c}.").replace(f"({e})", f"({c})") for l in lines]
        return lines

    def ep_inst(self):
        r = self.r
        g = self.fresh('g')
        o = self.fresh('g')
        e = self.fresh('e')
        setup = [f"let {g} = mk_g()", f"let {o} = mk_g()"]
        how = r.choice(['match', 'match', 'let_match', 'first'])
        refl, use = self.inst_ref(e)
        body = refl + self.wrap(self.inst_write(e, g, o)) + self.use_stmt(use, False)
        if self.ch(0.3):
            body = refl + self.inst_write(e, g, o) + self.inst_write(e, g, o) + self.use_stmt(use, False)
        idx = r.choice(["0", "1"])
        if how == 'match':
            out = [f"match find_n(&{g}, {idx}) {{", f"    Some({e}) => {{"] + ["        " + l for l in body] + ["    },", "    None => {}", "}"]
        elif how == 'let_match':
            out = [f"let {e} = match find_n(&{g}, {idx}) {{ Some(q) => q, None => &{o}.ns[0] }}"] + body
        else:
            out = [f"let {e} = first_n(&{g})"] + body
        return setup + self.wrap(out, ['plain', 'plain', 'block', 'clo', 'handle_note', 'if', 'apply'])

    def ep_loopref(self):
        r = self.r
        a, b, c = self.fresh('a'), self.fresh('b'), self.fresh('c')
        ra, rb = self.fresh('r'), self.fresh('q')
        setup = [f"let {a} = mk_v()", f"let {b} = mk_v()", f"let {c} = mk_v()", f"let {ra} = &{a}[0]", f"let {rb} = &{b}[1]"]
        stmts = [f"let t{ra} = {ra}\n{ra} = {rb}\n{rb} = t{ra}", f"{ra} = {rb}", f"{rb} = &{c}[0]", f"{ra} = &{a}[1]",
                 f"if i > 0 {{ {ra} = &{c}[1] }}", f"{a}.push(1)", f"{b}.clear()\n{b}.push(5)\n{b}.push(6)",
                 f"{c}.push(2)", f"print({ra})", f"print({rb})", f"{a} = mk_v()",
                 f"let g{ra} = || {ra} = {rb}\ng{ra}()", f"{ra} = id({rb})",
                 f"match pick_opt(&{c}, i == 0) {{ Some(z) => {ra} = z, None => {{}} }}",
                 f"{rb} = first(&{a})", f"if i == 1 {{ break }}", f"if i == 0 {{ continue }}"]
        body = []
        for _ in range(r.randint(2, 5)):
            body += r.choice(stmts).split("\n")
        kind = r.choice(['for', 'while', 'loop'])
        if kind == 'for':
            loop = ["for i in 0..3 {"] + ["    " + l for l in body] + ["}"]
        elif kind == 'while':
            loop = ["let i = 0", "while i < 3 {", "    i += 1"] + ["    " + l for l in body] + ["}"]
        else:
            loop = ["let i = 0", "loop {", "    i += 1", "    if i > 3 { break }"] + ["    " + l for l in body] + ["}"]
        if kind != 'for':
            loop = [l.replace("if i == 0 { continue }", "if i == 1 { continue }") for l in loop]
        after = r.choice([[f"print({ra})"], [f"print({rb})"], [f"print({ra})", f"print({rb})"],
                          [f"{a}.clear()", f"print({rb})"], [f"{c}.clear()", f"print({ra})"]])
        return setup + self.wrap(loop) + self.wrap(after)

    def ep_taskh(self):
        r = self.r
        v = self.fresh('v')
        n = self.fresh('n')
        s = self.fresh('s')
        setup = [f"let {v} = mk_v()", f"let {n} = 0"]
        wr = r.choice([f"{v}.push(1)", f"{n} += 1", f"{v}.clear()", f"grow(&{v})"])
        rd = r.choice([f"print({v}.len())", f"print({n})", f"print({v}[0])", f"show_v(&{v})", f"{n} += 2",
                       f"{v}.push(3)", f"let _ = &{v}[0]"])
        a = f"{s}.spawn(|| {{ {wr} }})"
        bt = f"{s}.spawn(|| print(0))"
        shape = r.choice([
            [f"let p = ({a}, {bt})", "let (x, y) = p", "y.join()", rd, "x.join()"],
            [f"let p = ({a}, {bt})", "let (x, y) = p", "x.join()", rd, "y.join()"],
            [f"let p = ({bt}, {a})", "let (x, y) = p", "x.join()", rd, "y.join()"],
            [f"let o = Some({a})", f"match o {{ Some(t) => t.join(), None => {{}} }}", rd],
            [f"let o = Some({a})", rd, f"match o {{ Some(t) => t.join(), None => {{}} }}"],
            [f"let t = if 1 < 2 {{ {a} }} else {{ {bt} }}", "t.join()", rd],
            [f"let t = if 1 < 2 {{ {bt} }} else {{ {a} }}", "t.join()", rd],
            [f"let x = {a}", f"let y = {bt}", "let z = x", "x = y", "y = z", "x.join()", rd, "y.join()"],
            [f"let x = {a}", f"let y = {bt}", "let z = x", "x = y", "y = z", "y.join()", rd, "x.join()"],
            [f"let x = {bt}", "for i in 0..2 {", "    x.join()", f"    x = {a}", "}", rd, "x.join()"],
            [f"let x = {a}", "let g = || x.join()", "g()", rd],
            [f"let x = {a}", "join_it(x)", rd],
            [f"let x = {a}", "let w = id(x)", "w.join()", rd],
            [f"let x = {a}", "let b = Box.new(x)", rd, "print(0)"],
            [f"let x = {a}", "handle Note { fn note(q) { x.join(); resume(()) } } in { note(1) }", rd],
            [f"let x = {a}", "apply(|| x.join())", rd],
            [f"let x = {a}", "x.detach()", rd],
        ])
        body = [f"scope {{ {s} =>"] + ["    " + l for l in shape] + ["}"]
        return setup + self.wrap(body, ['plain', 'plain', 'block', 'clo', 'if', 'handle_note', 'apply'])

    def episode(self):
        k = self.r.choice(['inst', 'inst', 'inst', 'loopref', 'loopref', 'taskh', 'taskh', 'ref', 'task'])
        return getattr(self, 'ep_' + k)()

    def program(self):
        body = []
        for _ in range(self.r.randint(1, 2)):
            ep = self.episode()
            body += ep
        lines = ["fn main() {"] + ["    " + l for b in body for l in b.split("\n")] + ["}"]
        pre = PRE + ("effect Pick { multi fn pick() -> bool }\n" if self.uses_pick else "")
        return pre + "\n" + "\n".join(self.extra_fns) + "\n" + "\n".join(lines) + "\n"


def generate(seed):
    return G4(seed).program()


if __name__ == "__main__":
    import sys
    print(generate(int(sys.argv[1]) if len(sys.argv) > 1 else 1))
