#!/usr/bin/env python3
"""Compositional generator for review round 3 (lens oracle).

A program is the prelude `lib/pre3.wf` and a `main` (or a few functions) made
of episodes. Each episode makes a fresh object, makes a reference, a closure,
a task or a linear value through one of many channels, runs a hazard through
one of many channels (direct, callee, closure, stored closure, handler clause,
task, fork, returned closure, Rc clone, multi resume, abort), and then uses
the value through one of many channels. Wrappers (if, loop, block, closure,
handle, scope, with_timeout) nest the parts. Most programs type-check, so the
checker decides on the hazard, and the oracle shows whether the hazard is real.
"""
import os
import random

HERE = os.path.dirname(os.path.abspath(__file__))
PRE = open(os.path.join(HERE, "lib/pre3.wf")).read()
OFF = set(filter(None, os.environ.get("GEN_OFF", "").split(",")))


class G:
    def __init__(self, seed):
        self.r = random.Random(seed)
        self.n = 0
        self.uses_pick = False
        self.extra_fns = []
        self.handled = []   # effects with a local handler around the current code

    def fresh(self, p):
        self.n += 1
        return f"{p}{self.n}"

    def ch(self, p):
        return self.r.random() < p

    def pick(self, xs):
        xs = [x for x in xs if x is not None]
        return self.r.choice(xs)

    # ------------------------------------------------------------------ wrappers
    def wrap(self, body, kinds=None):
        """Wraps a list of lines in a construct that runs it (at least once)."""
        r = self.r
        ks = kinds or ['plain', 'plain', 'if', 'block', 'loop1', 'loop2', 'clo', 'apply', 'handle_note',
                       'handle_ask', 'scope', 'timeout', 'match', 'while', 'clo_ret', 'labeled']
        ks = [k for k in ks if k not in OFF]
        k = r.choice(ks)
        ind = lambda ls: ["    " + l for l in ls]
        if k == 'plain':
            return body
        if k == 'if':
            c = r.choice(["true", "1 < 2", "mk_v().len() > 1"])
            out = [f"if {c} {{"] + ind(body)
            if self.ch(0.3):
                out += ["} else {", "    print(0)"]
            return out + ["}"]
        if k == 'block':
            return ["{"] + ind(body) + ["}"]
        if k == 'loop1':
            return ["loop {"] + ind(body) + ["    break", "}"]
        if k == 'loop2':
            i = self.fresh('i')
            return [f"for {i} in 0..2 {{"] + ind(body) + ["}"]
        if k == 'while':
            c = self.fresh('c')
            return [f"let {c} = 0", f"while {c} < 1 {{", f"    {c} += 1"] + ind(body) + ["}"]
        if k == 'clo':
            g = self.fresh('g')
            return [f"let {g} = || {{"] + ind(body) + ["}", f"{g}()"]
        if k == 'clo_ret':
            g = self.fresh('g')
            return [f"let {g} = || {{"] + ind(body) + ["    0", "}", f"print({g}())"]
        if k == 'apply':
            return ["apply(|| {"] + ind(body) + ["})"]
        if k == 'handle_note':
            self.handled.append('Note')
            return ["handle Note { fn note(x) { print(x); resume(()) } } in {"] + ind(body) + ["    note(1)", "}"]
        if k == 'handle_ask':
            return ["let _ = handle Ask { fn ask() { resume(4) } } in {"] + ind(body) + ["    ask()", "}"]
        if k == 'scope':
            s = self.fresh('s')
            return [f"scope {{ {s} =>"] + ind(body) + ["    print(0)", "}"]
        if k == 'timeout':
            return ["with_timeout(50.s) {"] + ind(body) + ["}"]
        if k == 'match':
            x = self.fresh('x')
            return [f"match Some(1) {{", f"    Some({x}) => {{"] + ["    " + l for l in ind(body)] + ["    },", "    None => {}", "}"]
        if k == 'labeled':
            return ["let _ = {"] + ind(body) + ["    0", "}"]
        return body

    # ------------------------------------------------------------------ objects
    def obj(self):
        """A fresh object: (kind, name, setup lines)."""
        k = self.r.choice(['v', 'v', 'v', 'w', 'w', 'rc', 'two'])
        nm = self.fresh(k)
        if k == 'v':
            return k, nm, [f"let {nm} = {self.r.choice(['mk_v()', '[1, 2, 3]'])}"]
        if k == 'w':
            return k, nm, [f"let {nm} = mk_w()"]
        if k == 'rc':
            return k, nm, [f"let {nm} = mk_r()"]
        return k, nm, [f"let {nm} = Two {{ a: mk_v(), b: mk_v() }}"]

    def vec_of(self, k, nm):
        """A place of type Vec<u64> in the object, and a disjoint one (or None)."""
        if k == 'v':
            return nm, None
        if k == 'w':
            return f"{nm}.ns", None
        if k == 'rc':
            return f"{nm}.items", None
        return self.r.choice([(f"{nm}.a", f"{nm}.b"), (f"{nm}.b", f"{nm}.a")])

    # ------------------------------------------------------------------ references
    def make_ref(self, k, nm):
        """Lines that bind a name to a reference into the object, the use expression, and the vec place."""
        r = self.r
        vp, other = self.vec_of(k, nm)
        x = self.fresh('r')
        opts = [
            ([f"let {x} = &{vp}[0]"], f"{x}"),
            ([f"let {x} = {vp}.get(1)"], f"{x}"),
            ([f"let {x} = first(&{vp})"], f"{x}"),
            ([f"let {x} = id(&{vp}[0])"], f"{x}"),
            ([f"let {x} = pass_ref(&{vp}[1])"], f"{x}"),
            ([f"let ({x}, _) = pair_of(&{vp})"], f"{x}"),
            ([f"let {x} = match pick_opt(&{vp}, true) {{ Some(q) => q, None => &{vp}[0] }}"], f"{x}"),
            ([f"let t{x} = (&{vp}[0], 1)", f"let ({x}, _) = t{x}"], f"{x}"),
            ([f"let rs{x} = Vec.new()", f"rs{x}.push(&{vp}[0])", f"let {x} = rs{x}[0]"], f"{x}"),
            ([f"let rs{x} = Vec.new()", f"keep(&rs{x}, &{vp}[1])", f"let {x} = rs{x}[0]"], f"{x}"),
            ([f"let o{x} = Some(&{vp}[0])"], f"match o{x} {{ Some(q) => q + 0, None => 0 }}"),
            ([f"let {x} = || {vp}[0]"], f"{x}()"),
            ([f"let {x} = || {vp}.len()"], f"{x}()"),
            ([f"let f{x} = make_reader(&{vp})"], None),
            ([f"let {x} = &{vp}"], f"{x}.len()"),
            ([f"let {x} = &{vp}"], f"{x}[0]"),
        ]
        if k == 'w':
            opts += [
                ([f"let {x} = &{nm}.es[0].hp"], f"{x}"),
                ([f"let {x} = &{nm}.b.hp"], f"{x}"),
                ([f"let e{x} = first_e(&{nm})", f"let {x} = &e{x}.hp"], f"{x}"),
                ([f"let e{x} = {nm}.top()"], f"e{x}.hp"),
                ([f"let {x} = match get_e(&{nm}, true) {{ Some(q) => q, None => &{nm}.es[0] }}"], f"{x}.hp"),
                ([f"let {x} = &{nm}.b"], f"{x}.hp"),
            ]
        if k == 'rc':
            opts += [([f"let {x} = &{nm}.n"], f"{x}"), ([f"let c{x} = {nm}.clone()", f"let {x} = &c{x}.items[0]"], f"{x}")]
        lines, use = r.choice(opts)
        if use is None:
            use = f"f{x}()"
            return lines, use, vp, other, True
        return lines, use, vp, other, False

    def use_stmt(self, use, is_unit):
        """Lines that use a value expression through a channel."""
        r = self.r
        if is_unit:
            e = use
            opts = [[e], [f"apply(|| {e})"], [f"let u{self.n} = || {e}", f"u{self.n}()"]]
            self.n += 1
            return r.choice(opts)
        opts = [
            [f"print({use})"],
            [f"print({use} + 1)"],
            [f"let u{self.n} = || print({use})", f"u{self.n}()"],
            [f"apply(|| print({use}))"],
            [f"twice(|| print({use}))"],
            [f"let y{self.n} = {use}", f"print(y{self.n})"],
            ["handle Note { fn note(x) { print(" + use + "); resume(()) } } in {", "    note(1)", "}"],
            [f"scope {{ s{self.n} => s{self.n}.spawn(|| print({use})) }}", "print(0)"],
            [f"spawn_join(|| print({use}))"],
        ]
        self.n += 1
        return r.choice(opts)

    def hazard(self, k, nm, vp, other, bad=True):
        """Lines that change the vec place `vp` (bad) or a disjoint/stable part (good)."""
        r = self.r
        if not bad:
            opts = []
            if other:
                opts += [f"{other}.push(5)", f"{other}.clear()", f"grow(&{other})", f"apply(|| {other}.push(1))"]
            if k == 'w':
                opts += [f"{nm}.score += 1", f"{nm}.es[0].hp += 1", f"bump(&{nm}.es[1])"]
            if k == 'rc':
                opts += [f"{nm}.n += 1"]
            opts += [f"{vp}[0] = 7", f"print({vp}.len())", f"show_v(&{vp})", f"let m{self.n} = mk_v()"]
            self.n += 1
            return [r.choice(opts)]
        g = self.fresh('h')
        base = [f"{vp}.push(5)", f"{vp}.clear()\n{vp}.push(4)\n{vp}.push(6)", f"let _ = {vp}.pop()", f"grow(&{vp})", f"clear_v(&{vp})\n{vp}.push(4)\n{vp}.push(6)",
                f"grow_n(n: 3, v: &{vp})", f"{vp} = mk_v()"]
        if k == 'v':
            base += [f"print(take_v({nm}))", f"let m{g} = {nm}", f"{nm} = [4, 5]"]
        if k == 'w':
            base += [f"{nm}.add(2)", f"{nm} = mk_w()", f"print(take_w({nm}))"]
        if k == 'rc':
            base += [f"let c{g} = {nm}.clone()\nc{g}.items.push(1)", f"{nm} = mk_r()"]
        h = r.choice(base)
        hl = h.split("\n")
        chan = r.choice(['direct', 'direct', 'clo', 'apply', 'twice', 'stored', 'field', 'ret', 'handler', 'task',
                         'task_join', 'fork', 'spawn_it', 'each', 'ifclo', 'loopclo', 'idclo', 'calls', 'run_op',
                         'fnitem'])
        if chan in OFF:
            chan = 'direct'
        if chan == 'direct':
            return hl
        if chan == 'clo':
            return [f"let {g} = || {{"] + ["    " + l for l in hl] + ["}", f"{g}()"]
        if chan == 'apply':
            return ["apply(|| {"] + ["    " + l for l in hl] + ["})"]
        if chan == 'twice':
            return ["twice(|| {"] + ["    " + l for l in hl] + ["})"]
        if chan == 'stored':
            return [f"let fs{g} = Vec.new()", f"store_f(&fs{g}, || {{"] + ["    " + l for l in hl] + ["})", f"call_all(&fs{g})"]
        if chan == 'field':
            return [f"let hh{g} = H {{ f: || {{"] + ["    " + l for l in hl] + ["} }", f"call_h(&hh{g})"]
        if chan == 'ret':
            if h == f"{vp}.push(5)" or h == f"grow(&{vp})":
                return [f"let {g} = make_pusher(&{vp})", f"{g}()"]
            return [f"let {g} = || {{"] + ["    " + l for l in hl] + ["}", f"let k{g} = id({g})", f"k{g}()"]
        if chan == 'handler':
            return ["handle Note { fn note(x) {"] + ["    " + l for l in hl] + ["    resume(())", "} } in {", "    note(1)", "}"]
        if chan == 'run_op':
            return ["handle Run { fn run(f) { f(); resume(()) } } in {", "    run(|| {"] + ["        " + l for l in hl] + ["    })", "}"]
        if chan == 'task':
            s = self.fresh('s')
            return [f"scope {{ {s} =>", f"    {s}.spawn(|| {{"] + ["        " + l for l in hl] + ["    })", "}", "print(0)"]
        if chan == 'task_join':
            s = self.fresh('s')
            return [f"scope {{ {s} =>", f"    let t{g} = {s}.spawn(|| {{"] + ["        " + l for l in hl] + ["    })", f"    t{g}.join()", "}"]
        if chan == 'spawn_it':
            return ["spawn_it(|| {"] + ["    " + l for l in hl] + ["})"]
        if chan == 'fork':
            return ["fork_it(|| {"] + ["    " + l for l in hl] + ["}, || print(0))"]
        if chan == 'each':
            return [f"each(&[1, 2], |x: &u64| {{"] + ["    " + l for l in hl] + ["})"]
        if chan == 'ifclo':
            return [f"let {g} = if 1 < 2 {{ || {{"] + ["    " + l for l in hl] + ["} } else { || print(0) }", f"{g}()"]
        if chan == 'loopclo':
            return [f"let {g} = || print(0)", "for j in 0..2 {", f"    {g}()", f"    {g} = || {{"] + ["        " + l for l in hl] + ["    }", "}"]
        if chan == 'idclo':
            return [f"let {g} = id(|| {{"] + ["    " + l for l in hl] + ["})", f"{g}()"]
        if chan == 'calls':
            return [f"let cs{g} = Calls {{ fs: Vec.new() }}", f"cs{g}.fs.push(|| {{"] + ["    " + l for l in hl] + ["})", f"call_all(&cs{g}.fs)"]
        if chan == 'fnitem':
            if h == f"grow(&{vp})":
                return [f"let {g} = grow", f"{g}(&{vp})"]
            return hl
        return hl

    # ------------------------------------------------------------------ episodes
    def ep_ref(self):
        k, nm, setup = self.obj()
        lines, use, vp, other, unit = self.make_ref(k, nm)
        bad = self.ch(0.6)
        hz = self.hazard(k, nm, vp, other, bad)
        us = self.use_stmt(use, unit)
        shape = self.r.choice(['seq', 'seq', 'wrap_hz', 'wrap_use', 'wrap_all', 'wrap_ref_hz', 'hz_first'])
        if shape == 'seq':
            body = lines + hz + us
        elif shape == 'wrap_hz':
            body = lines + self.wrap(hz) + us
        elif shape == 'wrap_use':
            body = lines + hz + self.wrap(us)
        elif shape == 'wrap_all':
            body = self.wrap(lines + self.wrap(hz) + us)
        elif shape == 'wrap_ref_hz':
            body = self.wrap(lines + hz) + ([] if lines[0].startswith("let f") else []) + []
            body = lines + self.wrap(hz + us)
        else:
            body = hz + lines + us
        return setup + body

    def ep_move(self):
        """A value moves through a channel; a later use of the variable or of a closure or reference."""
        r = self.r
        nm = self.fresh('v')
        setup = [f"let {nm} = mk_v()"]
        pre = r.choice([[], [f"let q{nm} = &{nm}[0]"], [f"let c{nm} = || print({nm}.len())"],
                        [f"let c{nm} = make_reader(&{nm})"]])
        mv = r.choice([
            [f"print(take_v({nm}))"],
            [f"let m{nm} = {nm}"],
            [f"let m{nm} = || print(take_v({nm}))", f"m{nm}()"],
            [f"let m{nm} = || print(take_v({nm}))"],
            [f"apply(|| print(take_v({nm})))"],
            [f"let o{nm} = Some({nm})"],
            [f"let t{nm} = ({nm}, 1)"],
            [f"let b{nm} = Box.new({nm})"],
            [f"let w{nm} = Two {{ a: {nm}, b: mk_v() }}"],
            [f"scope {{ s{nm} => s{nm}.spawn(|| print(take_v({nm}))) }}"],
            [f"let fs{nm} = Vec.new()", f"fs{nm}.push({nm})"],
            [f"{{ {nm} }}"],
            [f"let _ = if true {{ {nm} }} else {{ mk_v() }}"],
            [f"let _ = match 1 {{ 1 => {nm}, _ => mk_v() }}"],
            [f"{nm}"],
            [f"let _ = {nm}"],
            [f"let rf{nm} = id({nm})"],
            [f"let _ = handle Note {{ fn note(x) {{ resume(()) }} }} in {{ {nm} }}"],
            [f"let k{nm} = || {{ let z = {nm}; z.len() }}"],
        ])
        after = r.choice([[], [f"{nm} = mk_v()"], [f"{nm} = [7]"]]) if self.ch(0.4) else []
        if pre and pre[0].startswith(f"let q{nm}"):
            use = [f"print(q{nm})"]
        elif pre:
            use = [f"c{nm}()"]
        else:
            use = [r.choice([f"print({nm}.len())", f"print({nm})", f"show_v(&{nm})", f"{nm}.push(1)"])]
        body = pre + self.wrap(mv) + after + self.wrap(use)
        return setup + body

    def ep_lin(self):
        """A linear value with hazards between its making and its consumer."""
        r = self.r
        t = self.fresh('t')
        kind = r.choice(['Tx', 'Lk'])
        fin = f"commit({t})" if kind == 'Tx' else f"unlock({t})"
        setup = [f"let {t} = {kind} {{ id: {self.n} }}"]
        haz = r.choice([
            [], [], ["maybe_fail(1)"], ["maybe_fail(500)"],
            ["let _ = handle Ask { fn ask() { 3 } } in {", "    print(ask())", "    0", "}"],
            ["let _ = handle Ask { fn ask() { 3 } } in { ask() }"],
            ["with_timeout(5.s) { print(1) }"],
            ["handle Note { fn note(x) { print(x) } } in {", "    note(1)", "}"],
            ["handle Fail { fn fail(m) { print(m) } } in {", "    maybe_fail(500)", "}"],
            ["scope { sq => sq.spawn(|| maybe_fail(1)) }", "print(0)"],
        ])
        cons = r.choice([
            [fin],
            [f"let g{t} = || {fin}", f"g{t}()"],
            [f"apply(|| {fin})"],
            [f"let o{t} = Some({t})", f"match o{t} {{ Some(z) => {'commit(z)' if kind == 'Tx' else 'unlock(z)'}, None => {{}} }}"],
            [f"scope {{ s{t} => s{t}.spawn(|| {fin}) }}", "print(0)"],
            [f"scope {{ s{t} => let j{t} = s{t}.spawn(|| {fin}); j{t}.join() }}"],
            ["handle Note { fn note(x) { " + fin + "; resume(()) } } in {", "    note(1)", "}"],
            ["handle Note { fn note(x) { resume(()) } } in {", "    note(1)", "    " + fin, "}"],
            [f"if 1 < 2 {{ {fin} }} else {{ {fin} }}"],
            [f"if 1 < 2 {{ {fin} }}"],
            [f"let b{t} = Box.new({t})"],
            [f"let z{t} = id({t})", f"{'commit' if kind == 'Tx' else 'unlock'}(z{t})"],
            [f"let _ = fork(|| {fin}, || print(0))"],
            ["let _ = handle Ask { fn ask() { " + fin + "; 3 } } in {", "    print(ask())", "    0", "}"],
            ["let _ = handle Ask { fn ask() { 3 } } in {", "    print(ask())", "    " + fin, "    0", "}"],
            [f"let tt{t} = ({t}, 1)", f"let (z{t}, _) = tt{t}", f"{'commit' if kind == 'Tx' else 'unlock'}(z{t})"],
            [f"for i in 0..1 {{ {fin} }}"],
            [f"loop {{ {fin}; break }}"],
            [f"twice(|| {fin})"],
        ])
        return setup + self.wrap(haz) + self.wrap(cons)

    def ep_task(self):
        """Two tasks, or a task and its parent, touch one object."""
        r = self.r
        k, nm, setup = self.obj()
        vp, other = self.vec_of(k, nm)
        n = self.fresh('n')
        setup = setup + [f"let {n} = 0"]
        acc = [f"{vp}.push(1)", f"print({vp}.len())", f"{n} += 1", f"print({n})", f"print({vp}[0])",
               f"grow(&{vp})", f"show_v(&{vp})", f"let _ = {vp}.get(0)", f"{vp}[0] = 5", f"print({vp})",
               f"apply(|| {vp}.push(2))", f"let q{n} = &{vp}[0]"]
        if other:
            acc += [f"{other}.push(1)", f"print({other}.len())"]
        if k == 'w':
            acc += [f"{nm}.score += 1", f"print({nm}.score)", f"{nm}.es[0].hp += 1", f"print({nm}.es[0].hp)"]
        a = "{ " + r.choice(acc) + " }"
        b = r.choice(acc)
        s = self.fresh('s')
        t = self.fresh('t')
        form = r.choice(['spawn_parent', 'spawn_parent_join', 'two_spawn', 'fork', 'fork_it', 'spawn_two',
                         'spawn_it_parent', 'join_helper', 'detach', 'tuple_handle', 'loop_spawn', 'clo_spawn',
                         'spawn_in_handler', 'nested_scope'])
        if form in OFF:
            form = 'spawn_parent'
        if form == 'spawn_parent':
            body = [f"scope {{ {s} =>", f"    {s}.spawn(|| {a})", f"    {b}", "}", "print(0)"]
        elif form == 'spawn_parent_join':
            pos = r.choice(['before', 'after'])
            body = [f"scope {{ {s} =>", f"    let {t} = {s}.spawn(|| {a})"]
            body += ([f"    {t}.join()", f"    {b}"] if pos == 'before' else [f"    {b}", f"    {t}.join()"])
            body += ["}"]
        elif form == 'two_spawn':
            body = [f"scope {{ {s} =>", f"    {s}.spawn(|| {a})", f"    {s}.spawn(|| {{ {b} }})", "}", "print(0)"]
        elif form == 'fork':
            body = [f"let _ = fork(|| {a}, || {{ {b} }})"]
        elif form == 'fork_it':
            body = [f"fork_it(|| {a}, || {{ {b} }})"]
        elif form == 'spawn_two':
            body = [f"spawn_two(|| {a}, || {{ {b} }})"]
        elif form == 'spawn_it_parent':
            body = [f"spawn_it(|| {a})", b]
        elif form == 'join_helper':
            body = [f"scope {{ {s} =>", f"    let {t} = {s}.spawn(|| {a})", f"    join_it({t})", f"    {b}", "}"]
        elif form == 'detach':
            body = [f"scope {{ {s} =>", f"    let {t} = {s}.spawn(|| {a})", f"    {t}.detach()", f"    {b}", "}"]
        elif form == 'tuple_handle':
            body = [f"scope {{ {s} =>", f"    let p{t} = ({s}.spawn(|| {a}), 1)", f"    let ({t}, _) = p{t}",
                    f"    {t}.join()", f"    {b}", "}"]
        elif form == 'loop_spawn':
            body = [f"scope {{ {s} =>", "    for i in 0..2 {", f"        {s}.spawn(|| {a})", "    }", f"    {b}", "}"]
        elif form == 'clo_spawn':
            body = [f"scope {{ {s} =>", f"    let g{t} = || {s}.spawn(|| {a})", f"    g{t}()", f"    {b}", "}"]
        elif form == 'spawn_in_handler':
            body = [f"scope {{ {s} =>", f"    handle Note {{ fn note(x) {{ {s}.spawn(|| {a}); resume(()) }} }} in {{",
                    "        note(1)", f"        {b}", "    }", "}"]
        else:
            s2 = self.fresh('s')
            body = [f"scope {{ {s} =>", f"    scope {{ {s2} =>", f"        {s}.spawn(|| {a})", "    }", f"    {b}", "}"]
        return setup + self.wrap(body, ['plain', 'plain', 'if', 'block', 'clo', 'apply', 'handle_note'])

    def ep_eff(self):
        """A closure that performs an operation goes outside its handler."""
        r = self.r
        g = self.fresh('e')
        op = r.choice(["print(ask())", "note(2)", "{ let _ = ask() }"])
        eff = 'Ask' if 'ask' in op else 'Note'
        clause = "fn ask() { resume(5) }" if eff == 'Ask' else "fn note(x) { resume(()) }"
        esc = r.choice([
            [f"let {g} = || print(0)", f"handle {eff} {{ {clause} }} in {{", f"    {g} = || {op}", "}", f"{g}()"],
            [f"let {g} = handle {eff} {{ {clause} }} in {{ || {op} }}", f"{g}()"],
            [f"let fs{g} = Vec.new()", f"handle {eff} {{ {clause} }} in {{", f"    fs{g}.push(|| {op})", "}", f"call_all(&fs{g})"],
            [f"let hh{g} = H {{ f: || print(0) }}", f"handle {eff} {{ {clause} }} in {{", f"    hh{g} = H {{ f: || {op} }}", "}", f"call_h(&hh{g})"],
            [f"let {g} = handle {eff} {{ {clause} }} in {{ let k = || {op}; id(k) }}", f"{g}()"],
            [f"handle {eff} {{ {clause} }} in {{", f"    scope {{ s{g} => s{g}.spawn(|| {op}) }}", "}"],
            [f"handle {eff} {{ {clause} }} in {{", f"    spawn_it(|| {op})", "}"],
            [f"handle {eff} {{ {clause} }} in {{", f"    let _ = fork(|| {op}, || print(1))", "}"],
            [f"let {g} = handle {eff} {{ {clause} }} in {{ Some(|| {op}) }}", f"match {g} {{ Some(z) => z(), None => {{}} }}"],
            [f"let {g} = handle {eff} {{ {clause} }} in {{ (|| {op}, 1) }}", f"let (z{g}, _) = {g}", f"z{g}()"],
            [f"let rc{g} = Rc.new(Calls {{ fs: Vec.new() }})", f"handle {eff} {{ {clause} }} in {{", f"    rc{g}.fs.push(|| {op})", "}", f"call_all(&rc{g}.fs)"],
            [f"let {g} = handle {eff} {{ {clause} }} in {{ make_op_closure() }}", f"{g}()"],
            [f"handle {eff} {{ {clause} }} in {{", f"    {op}", "}"],
        ])
        if any("make_op_closure" in l for l in esc):
            self.extra_fns.append("fn make_op_closure() -> fn() / Ask { || print(ask()) }" if eff == 'Ask'
                                  else "fn make_op_closure() -> fn() / Note { || note(3) }")
            self.extra_fns = list(dict.fromkeys(self.extra_fns))
        return esc

    def ep_cont(self):
        """Continuation shapes: resume counts, multi with values live across."""
        r = self.r
        self.uses_pick = True
        nm = self.fresh('v')
        body = r.choice([
            [f"let {nm} = mk_v()", "handle Pick { fn pick() { resume(true); resume(false) } } in {",
             f"    let r{nm} = &{nm}[0]", "    let b = pick()", f"    if b {{ {nm}.push(1) }} else {{ print(r{nm}) }}", "}"],
            [f"let {nm} = Tx {{ id: 1 }}", "handle Pick { fn pick() { resume(true); resume(false) } } in {",
             "    let b = pick()", f"    if b {{ commit({nm}) }}", "}"],
            [f"let {nm} = mk_v()", "handle Pick { fn pick() { resume(true); resume(false) } } in {",
             "    let b = pick()", f"    if b {{ print(take_v({nm})) }}", "}"],
            [f"let {nm} = mk_v()", "handle Pick { fn pick() { resume(true); resume(false) } } in {",
             f"    let m{nm} = {nm}", "    let b = pick()", f"    print(m{nm}.len())", "}"],
            [f"let {nm} = mk_v()", "handle Pick { fn pick() { resume(true); " + nm + ".clear(); resume(false) } } in {",
             f"    let r{nm} = &{nm}[0]", "    if pick() { print(1) }", f"    print(r{nm})", "}"],
            [f"let {nm} = Tx {{ id: 2 }}", "handle Pick { fn pick() { resume(true); resume(false) } } in {",
             "    if pick() { print(1) }", "}", f"commit({nm})"],
            [f"let {nm} = Lk {{ id: 2 }}", "handle Pick { fn pick() { resume(true); resume(false) } } in {",
             f"    let z{nm} = {nm}", "    if pick() { print(1) }", f"    unlock(z{nm})", "}"],
            [f"let {nm} = Lk {{ id: 2 }}", "let g = || {", "    handle Pick { fn pick() { resume(true); resume(false) } } in {",
             "        if pick() { print(1) }", "    }", "}", "g()", f"unlock({nm})"],
            [f"let {nm} = mk_v()", "handle Pick { fn pick() { resume(true); resume(false) } } in {",
             "    let b = pick()", f"    apply(|| print(take_v({nm})))", "}"],
            [f"let {nm} = mk_v()", "handle Pick { fn pick() { resume(true); resume(false) } } in {",
             f"    let f{nm} = || print(take_v({nm}))", "    let b = pick()", f"    f{nm}()", "}"],
            [f"let {nm} = 0", "handle Pick { fn pick() { resume(true); resume(false) } } in {",
             f"    scope {{ s{nm} =>", f"        s{nm}.spawn(|| {nm} += 1)", "        let b = pick()", "    }", "}"],
            [f"let {nm} = mk_v()", "handle Pick { fn pick() { let a = resume(true); resume(false) } } in {",
             "    let b = pick()", f"    let k{nm} = Tx {{ id: 3 }}", f"    commit(k{nm})", "}"],
            ["handle Pick { fn pick() { resume(true); resume(false) } } in {",
             f"    let k{nm} = Tx {{ id: 3 }}", "    let b = pick()", f"    commit(k{nm})", "}"],
            ["handle Pick { fn pick() { resume(true); resume(false) } } in {",
             f"    let k{nm} = Tx {{ id: 3 }}", f"    let g{nm} = || pick()", f"    let b = g{nm}()", f"    commit(k{nm})", "}"],
            ["handle Pick { fn pick() { resume(true); resume(false) } } in {",
             f"    let k{nm} = Tx {{ id: 3 }}", "    let b = pick_via()", f"    commit(k{nm})", "}"],
        ])
        if any("pick_via" in l for l in body):
            self.extra_fns.append("fn pick_via() -> bool / Pick { pick() }")
            self.extra_fns = list(dict.fromkeys(self.extra_fns))
        return self.wrap(body, ['plain', 'plain', 'block', 'clo', 'if'])

    def episode(self):
        ks = ['ref', 'ref', 'ref', 'ref', 'move', 'move', 'lin', 'lin', 'task', 'task', 'task', 'eff', 'cont']
        ks = [k for k in ks if k not in OFF]
        k = self.r.choice(ks)
        return getattr(self, 'ep_' + k)()

    def program(self):
        body = []
        for _ in range(self.r.randint(1, 3)):
            ep = self.episode()
            if self.ch(0.3):
                ep = self.wrap(ep, ['block', 'clo', 'handle_note', 'scope', 'loop1', 'if'])
            body += ep
        pre = PRE
        if self.uses_pick:
            pre += "effect Pick { multi fn pick() -> bool }\n"
        lines = ["fn main() {"] + ["    " + l for b in body for l in b.split("\n")] + ["}"]
        return pre + "\n" + "\n".join(self.extra_fns) + "\n" + "\n".join(lines) + "\n"


def generate(seed):
    return G(seed).program()


if __name__ == "__main__":
    import sys
    print(generate(int(sys.argv[1]) if len(sys.argv) > 1 else 1))
