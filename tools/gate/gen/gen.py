#!/usr/bin/env python3
"""Random Weft program generator for differential soundness testing.

Each program has a fixed prelude of types, effects and helpers, and a random
`main`. The generator keeps a typed environment, so most programs type-check.
Some operations are wrong on purpose (use after a move, a mutation between a
borrow and its use), so the checker must reject them.
"""
import os
import random

# Features that are off: known findings, so new runs find new shapes.
OFF = set(filter(None, os.environ.get("GEN_OFF", "").split(",")))

PRELUDE = r'''struct E { hp: u64, tag: u64 }
struct W { es: Vec<E>, ns: Vec<u64>, score: u64, b: Box<E> }
linear struct Tx { id: u64 }
    on abort = tx_abort
linear struct Lk { id: u64 }
effect Ask { fn ask() -> u64 }
effect Pick { multi fn pick() -> bool }
effect Note { fn note(x: u64) }
effect Grab { fn grab(r: &u64) -> u64 }

fn tx_abort(t: Tx) { let Tx(id) = t; print("abort", id) }
fn commit(t: Tx) { let Tx(id) = t; print("commit", id) }
fn unlock(l: Lk) { let Lk(id) = l; print("unlock", id) }
fn mk_e(n: u64) -> E { E { hp: n, tag: n } }
fn mk_w() -> W {
    let w = W { es: Vec.new(), ns: Vec.new(), score: 0, b: Box.new(E { hp: 1, tag: 0 }) }
    w.es.push(E { hp: 5, tag: 1 })
    w.es.push(E { hp: 6, tag: 2 })
    w.ns.push(1)
    w.ns.push(2)
    w
}
fn mk_v() -> Vec<u64> {
    let v = Vec.new()
    v.push(1)
    v.push(2)
    v.push(3)
    v
}
fn grow(v: &Vec<u64>) { v.push(9) }
fn grow_w(w: &W) { w.es.push(E { hp: 1, tag: 9 }) }
fn bump(e: &E) { e.hp += 1 }
fn bump_n(r: &u64) { r += 1 }
fn first(v: &Vec<u64>) -> &u64 in v[] { &v[0] }
fn first_e(w: &W) -> &E in w.es[] { &w.es[0] }
fn id<T>(x: T) -> T { x }
fn apply(f: fn()) { f() }
fn twice(f: fn()) { f(); f() }
fn take_v(v: Vec<u64>) -> usize { v.len() }
fn take_w(w: W) -> u64 { w.score }
fn sum(v: &Vec<u64>) -> u64 {
    let t = 0
    for x in v[] { t += x }
    t
}
fn call_with(f: fn(&u64), v: &Vec<u64>) { f(&v[0]) }
fn clear_then(v: &Vec<u64>, f: fn()) { v.clear(); f() }
fn ask_twice() -> u64 { ask() + ask() }
fn note_all(v: &Vec<u64>) { for x in v[] { note(x) } }
fn maybe_fail(n: u64) { if n > 100 { fail("big") } }
fn with_tx(id: u64) -> u64 {
    let t = Tx { id: id }
    let a = ask()
    commit(t)
    a
}
fn pass_ref(r: &u64) -> &u64 in r { r }
fn len_of(v: &Vec<u64>) -> usize { v.len() }
fn swap_in(dst: &Vec<u64>, src: Vec<u64>) { dst.clear(); for x in src[] { dst.push(x) } }
fn run_both(f: fn(), g: fn()) { f(); g() }
fn make_reader(v: &Vec<u64>) -> fn() { || print(v.len()) }
fn find(v: &Vec<u64>) -> Option<&u64 in v[]> { if v.len() > 0 { Some(&v[0]) } else { None } }
fn pair_of(v: &Vec<u64>) -> (&u64 in v[], u64) { (&v[0], 1) }
impl W {
    fn top(self) -> &E in self.es[] { &self.es[0] }
    fn add(self, n: u64) { self.ns.push(n) }
    fn total(self) -> u64 { let t = 0; for x in self.ns[] { t += x }; t }
}
fn sum_tx(t: &Tx) -> u64 { t.id }
fn each(v: &Vec<u64>, f: fn(&u64)) { for i in 0..v.len() { f(&v[i]) } }
'''


class Var:
    def __init__(self, name, kind, **kw):
        self.name = name
        self.kind = kind
        self.moved = False
        self.attrs = kw


class Gen:
    def __init__(self, seed, max_depth=3):
        self.r = random.Random(seed)
        self.n = 0
        self.frames = [[]]
        self.lines = []
        self.ind = 1
        self.max_depth = max_depth
        self.depth = 0
        self.handled = set()     # effects with a handler around
        self.scope_var = None    # name of the scope variable when in a scope body
        self.in_task = False
        self.in_closure = 0

    # ---------------------------------------------------------------- env
    def fresh(self, p):
        self.n += 1
        return f"{p}{self.n}"

    def add(self, name, kind, **kw):
        v = Var(name, kind, **kw)
        self.frames[-1].append(v)
        return v

    def vars(self, *kinds, live=True):
        out = []
        for fr in self.frames:
            for v in fr:
                if v.kind in kinds and (not live or not v.moved or self.r.random() < 0.04):
                    out.append(v)
        return out

    def pick(self, *kinds, live=True):
        vs = self.vars(*kinds, live=live)
        return self.r.choice(vs) if vs else None

    def wr(self, w):
        return w.name if w.attrs.get('isref') else f"&{w.name}"

    def emit(self, s):
        self.lines.append("    " * self.ind + s)

    def chance(self, p):
        return self.r.random() < p

    # ---------------------------------------------------------------- exprs
    def ref_expr(self):
        """An expression of type &u64, or None."""
        r = self.r
        opts = []
        v = self.pick('v')
        if v:
            opts += [f"&{v.name}[0]", f"&{v.name}[1]", f"{v.name}.get(0)", f"first(&{v.name})",
                     f"id(&{v.name}[0])", f"pass_ref(&{v.name}[0])"]
        w = self.pick('w')
        if w:
            opts += [f"&{w.name}.score", f"&{w.name}.ns[0]", f"&{w.name}.es[0].hp", f"&{w.name}.b.hp",
                     f"&{w.name}.es[1].tag", f"first(&{w.name}.ns)"]
        n = self.pick('n')
        if n:
            opts += [f"&{n.name}"]
        rv = self.pick('rv')
        if rv:
            opts += [f"&{rv.name}[0]", f"first({rv.name})"]
        re_ = self.pick('re')
        if re_:
            opts += [f"&{re_.name}.hp"]
        bx = self.pick('bx')
        if bx:
            opts += [f"&{bx.name}.hp"]
        rc = self.pick('rc')
        if rc:
            opts += [f"&{rc.name}.hp"]
        rr = self.pick('r')
        if rr:
            opts += [f"{rr.name}", f"pass_ref({rr.name})"]
        sl = self.pick('sl')
        if sl:
            opts += [f"&{sl.name}[0]"]
        return r.choice(opts) if opts else None

    def u64_expr(self):
        r = self.r
        opts = ["1", "2"]
        rr = self.pick('r')
        if rr:
            opts += [f"{rr.name} + 0", f"{rr.name}"]
        n = self.pick('n')
        if n:
            opts += [f"{n.name}", f"{n.name} + 1"]
        v = self.pick('v')
        if v:
            opts += [f"{v.name}[0]", f"sum(&{v.name})"]
        w = self.pick('w')
        if w:
            opts += [f"{w.name}.score", f"{w.name}.es[0].hp", f"{w.name}.b.hp"]
        re_ = self.pick('re')
        if re_:
            opts += [f"{re_.name}.hp"]
        if 'Ask' in self.handled:
            opts += ["ask()", "ask_twice()"]
        if 'Ask' in self.handled and 'Grab' in self.handled and rr:
            opts += [f"grab({rr.name})"]
        return r.choice(opts)

    def cond(self):
        opts = ["true", "false"]
        n = self.pick('n')
        if n:
            opts.append(f"{n.name} > 1")
        if 'Pick' in self.handled:
            opts += ["pick()"] * 2
        v = self.pick('v')
        if v:
            opts.append(f"{v.name}.len() > 2")
        return self.r.choice(opts)

    # ---------------------------------------------------------------- stmts
    def decl(self):
        r = self.r
        ks = ['v', 'v', 'w', 'w', 'n', 'r', 'r', 'r', 're', 'rv', 'f', 'f', 'f', 'tx', 'lk',
              'bx', 'rc', 'o', 'sl', 'fr', 'ff']
        k = r.choice([x for x in ks if x not in OFF])
        if k == 'v':
            nm = self.fresh('v')
            e = r.choice(["mk_v()", "[1, 2, 3]", "mk_v()"])
            self.emit(f"let {nm} = {e}")
            self.add(nm, 'v')
        elif k == 'w':
            nm = self.fresh('w')
            self.emit(f"let {nm} = mk_w()")
            self.add(nm, 'w')
        elif k == 'n':
            nm = self.fresh('n')
            self.emit(f"let {nm} = {self.u64_expr()}")
            self.add(nm, 'n')
        elif k == 'r':
            e = self.ref_expr()
            if not e:
                return self.decl_simple()
            nm = self.fresh('r')
            self.emit(f"let {nm} = {e}")
            self.add(nm, 'r')
        elif k == 're':
            w = self.pick('w')
            if not w:
                return self.decl_simple()
            nm = self.fresh('re')
            e = r.choice([f"&{w.name}.es[0]", f"first_e({self.wr(w)})", f"{w.name}.es.get(1)", f"&{w.name}.b",
                          f"id(&{w.name}.es[1])"])
            self.emit(f"let {nm} = {e}")
            self.add(nm, 're')
        elif k == 'rv':
            opts = []
            v = self.pick('v')
            if v:
                opts.append(f"&{v.name}")
            w = self.pick('w')
            if w:
                opts.append(f"&{w.name}.ns")
            if not opts:
                return self.decl_simple()
            nm = self.fresh('rv')
            self.emit(f"let {nm} = {r.choice(opts)}")
            self.add(nm, 'rv')
        elif k == 'f':
            self.decl_closure()
        elif k == 'fr':
            nm = self.fresh('fr')
            body = r.choice(["print(x)", "print(x + 1)"])
            v = self.pick('v')
            if v and self.chance(0.4):
                body = r.choice([f"{{ {v.name}.push(1); print(x) }}", f"{{ print(x); {v.name}.clear() }}"])
            self.emit(f"let {nm} = |x: &u64| {body}")
            self.add(nm, 'fr')
        elif k == 'ff':
            v = self.pick('v')
            if not v:
                return self.decl_simple()
            nm = self.fresh('f')
            self.emit(f"let {nm} = make_reader(&{v.name})")
            self.add(nm, 'f', once=False)
        elif k == 'tx':
            nm = self.fresh('tx')
            self.emit(f"let {nm} = Tx {{ id: {self.n} }}")
            self.add(nm, 'tx')
        elif k == 'lk':
            nm = self.fresh('lk')
            self.emit(f"let {nm} = Lk {{ id: {self.n} }}")
            self.add(nm, 'lk')
        elif k == 'bx':
            nm = self.fresh('bx')
            self.emit(f"let {nm} = Box.new(mk_e({self.n}))")
            self.add(nm, 'bx')
        elif k == 'rc':
            old = self.pick('rc')
            nm = self.fresh('rc')
            if old and self.chance(0.5):
                self.emit(f"let {nm} = {old.name}.clone()")
            else:
                self.emit(f"let {nm} = Rc.new(mk_e({self.n}))")
            self.add(nm, 'rc')
        elif k == 'o':
            nm = self.fresh('o')
            self.emit(f"let {nm} = {r.choice(['Some(3)', 'None', 'Some(4)'])}")
            self.add(nm, 'o')
        elif k == 'sl':
            v = self.pick('v')
            if not v:
                return self.decl_simple()
            a, b = self.fresh('sl'), self.fresh('sl')
            self.emit(f"let ({a}, {b}) = {v.name}.split_at(1)")
            self.add(a, 'sl')
            self.add(b, 'sl')

    def decl_simple(self):
        nm = self.fresh('v')
        self.emit(f"let {nm} = mk_v()")
        self.add(nm, 'v')

    def closure_body(self):
        """A short closure body. Returns (text, once, linear)."""
        r = self.r
        opts = []
        rr = self.pick('r')
        if rr:
            opts.append((f"print({rr.name})", False, False))
            opts.append((f"bump_n({rr.name})", False, False))
        v = self.pick('v')
        if v:
            opts.append((f"{v.name}.push(4)", False, False))
            opts.append((f"print({v.name}[0])", False, False))
            if 'clomove' not in OFF:
                opts.append((f"{{ let m = {v.name}; print(m.len()) }}", True, False))
            opts.append((f"{v.name}.clear()", False, False))
            if 'clomove' not in OFF:
                opts.append((f"print(take_v({v.name}))", True, False))
        n = self.pick('n')
        if n:
            opts.append((f"{n.name} += 1", False, False))
        w = self.pick('w')
        if w:
            opts.append((f"{w.name}.score += 1", False, False))
            opts.append((f"grow_w({self.wr(w)})", False, False))
            opts.append((f"print({w.name}.es[0].hp)", False, False))
        re_ = self.pick('re')
        if re_:
            opts.append((f"bump({re_.name})", False, False))
            opts.append((f"print({re_.name}.hp)", False, False))
        tx = self.pick('tx')
        if tx:
            opts.append((f"commit({tx.name})", True, True))
        rv = self.pick('rv')
        if rv:
            opts.append((f"grow({rv.name})", False, False))
        if 'Ask' in self.handled:
            opts.append(("print(ask())", False, False))
        if 'Note' in self.handled:
            opts.append(("note(5)", False, False))
        rr2 = self.pick('r')
        if rr2 and v:
            opts.append((f"{rr2.name} = &{v.name}[1]", False, False))
        if not opts:
            opts.append(("print(0)", False, False))
        return r.choice(opts)

    def decl_closure(self):
        nm = self.fresh('f')
        body, once, lin = self.closure_body()
        self.emit(f"let {nm} = || {body}")
        self.add(nm, 'f', once=once, lin=lin)

    def mutate(self):
        r = self.r
        opts = []
        v = self.pick('v')
        if v:
            opts += [f"{v.name}.push(7)", f"let _ = {v.name}.pop()", f"{v.name}.clear()", f"{v.name}[0] = 8",
                     f"grow(&{v.name})", f"{v.name} = mk_v()", f"{v.name}.push({v.name}[0])"]
        w = self.pick('w')
        if w:
            opts += [f"{w.name}.es.push(mk_e(3))", f"{w.name}.score += 1", f"{w.name}.es[0].hp += 1",
                     f"{w.name}.b = Box.new(mk_e(4))", f"grow_w({self.wr(w)})", f"{w.name}.ns.clear()",
                     f"{w.name}.ns.push(5)", f"{w.name}.b.hp += 1"] + ([] if w.attrs.get('isref') else [f"{w.name} = mk_w()"])
        re_ = self.pick('re')
        if re_:
            opts += [f"{re_.name}.hp += 1", f"bump({re_.name})"]
        rr = self.pick('r')
        if rr:
            opts += [f"{rr.name} += 1", f"bump_n({rr.name})"]
            e = self.ref_expr()
            if e:
                opts += [f"{rr.name} = {e}"]
        rv = self.pick('rv')
        if rv:
            opts += [f"grow({rv.name})", f"{rv.name}.push(6)", f"{rv.name}.clear()"]
        n = self.pick('n')
        if n:
            opts += [f"{n.name} += 1", f"{n.name} = 9"]
        bx = self.pick('bx')
        if bx:
            opts += [f"{bx.name} = Box.new(mk_e(2))", f"{bx.name}.hp += 1"]
        rc = self.pick('rc')
        if rc:
            opts += [f"{rc.name}.hp += 1", f"{rc.name} = Rc.new(mk_e(8))"]
        o = self.pick('o')
        if o:
            opts += [f"{o.name} = None", f"{o.name} = Some(6)"]
        if 'Note' in self.handled:
            opts += ["note(1)"]
        if 'Ask' in self.handled:
            opts += ["let _ = ask()"]
        if not opts:
            return self.decl()
        self.emit(r.choice(opts))

    def use(self):
        r = self.r
        opts = []
        rr = self.pick('r')
        if rr:
            opts += [f"print({rr.name})", f"print({rr.name} + 1)"]
        re_ = self.pick('re')
        if re_:
            opts += [f"print({re_.name}.hp)", f"print({re_.name})"]
        rv = self.pick('rv')
        if rv:
            opts += [f"print({rv.name}.len())", f"print(sum({rv.name}))", f"print(len_of({rv.name}))"]
        v = self.pick('v')
        if v:
            opts += [f"print({v.name}.len())", f"print(sum(&{v.name}))", f"print({v.name})"]
        w = self.pick('w')
        if w:
            opts += [f"print({w.name}.score)", f"print({w.name}.es.len())"]
        n = self.pick('n')
        if n:
            opts += [f"print({n.name})"]
        sl = self.pick('sl')
        if sl:
            opts += [f"print({sl.name}[0])"]
        bx = self.pick('bx')
        if bx:
            opts += [f"print({bx.name}.hp)"]
        rc = self.pick('rc')
        if rc:
            opts += [f"print({rc.name}.hp)"]
        o = self.pick('o')
        if o:
            opts += [f"match {o.name} {{ Some(x) => print(x), None => print(0) }}"]
        f = self.pick('f')
        if f:
            opts += [f"{f.name}()", f"apply({f.name})"]
            if 'twice' not in OFF:
                opts += [f"twice({f.name})"]
            if v:
                opts += [f"clear_then(&{v.name}, {f.name})"]
            g = self.pick('f')
            if g:
                opts += [f"run_both({f.name}, {g.name})"]
        fr = self.pick('fr')
        if fr:
            e = self.ref_expr()
            if e:
                opts += [f"{fr.name}({e})"]
            if v:
                opts += [f"call_with({fr.name}, &{v.name})"]
        if not opts:
            return self.decl()
        s = r.choice(opts)
        self.emit(s)
        # Mark moves of once closures.
        if f and s.startswith(f.name) and f.attrs.get('once'):
            f.moved = True

    def move(self):
        r = self.r
        opts = []
        v = self.pick('v')
        if v:
            opts.append(('v', v, f"let {{}} = {v.name}"))
            opts.append((None, v, f"print(take_v({v.name}))"))
            dst = self.pick('v')
            if dst and dst is not v:
                opts.append((None, v, f"swap_in(&{dst.name}, {v.name})"))
        w = self.pick('w')
        if w and w.attrs.get('isref'):
            w = None
        if w:
            opts.append(('w', w, f"let {{}} = {w.name}"))
            opts.append((None, w, f"print(take_w({w.name}))"))
        tx = self.pick('tx')
        if tx:
            opts.append((None, tx, f"commit({tx.name})"))
            opts.append((None, tx, f"let Tx(i{self.n}) = {tx.name}"))
            opts.append(('tx', tx, f"let {{}} = {tx.name}"))
            opts.append(('tx', tx, f"let {{}} = id({tx.name})"))
        lk = self.pick('lk')
        if lk:
            opts.append((None, lk, f"unlock({lk.name})"))
        bx = self.pick('bx')
        if bx:
            opts.append(('bx', bx, f"let {{}} = {bx.name}"))
        rc = self.pick('rc')
        if rc:
            opts.append((None, rc, f"let _ = {rc.name}"))
        if not opts:
            return self.decl()
        k, var, s = r.choice(opts)
        if k:
            nm = self.fresh(k)
            s = s.format(nm)
            self.emit(s)
            self.add(nm, k)
        else:
            self.emit(s)
        var.moved = True

    def finish_linears(self, frame):
        """Consumes the linear values of a frame on most paths."""
        for v in frame:
            if v.kind in ('tx', 'lk') and not v.moved:
                if self.chance(0.92):
                    self.emit(f"commit({v.name})" if v.kind == 'tx' else f"unlock({v.name})")
                    v.moved = True
            if v.kind == 'f' and v.attrs.get('lin') and not v.moved:
                if self.chance(0.9):
                    self.emit(f"{v.name}()")
                    v.moved = True

    # ---------------------------------------------------------------- blocks
    def block(self, n=None, finish=True):
        self.frames.append([])
        self.ind += 1
        self.depth += 1
        for _ in range(n if n is not None else self.r.randint(1, 4)):
            self.stmt()
        fr = self.frames.pop()
        if finish:
            self.finish_linears(fr)
        self.depth -= 1
        self.ind -= 1
        return fr

    def compound(self):
        r = self.r
        ks = ['if', 'if', 'for', 'forv', 'while', 'loop', 'blk', 'clo', 'apply', 'handle', 'handle',
              'handle', 'scope', 'scope', 'fork', 'match', 'retblk', 'twice']
        k = r.choice([x for x in ks if x not in OFF])
        if k == 'if':
            self.emit(f"if {self.cond()} {{")
            self.block()
            if self.chance(0.5):
                self.emit("} else {")
                self.block()
            self.emit("}")
        elif k == 'for':
            self.emit(f"for i{self.fresh('')} in 0..2 {{")
            self.block()
            self.emit("}")
        elif k == 'forv':
            v = self.pick('v', 'rv')
            if not v:
                return self.stmt_simple()
            x = self.fresh('x')
            self.emit(f"for {x} in {v.name}[] {{")
            self.frames.append([])
            self.add(x, 'n')
            self.ind += 1
            self.depth += 1
            for _ in range(self.r.randint(1, 3)):
                self.stmt()
            self.depth -= 1
            self.ind -= 1
            fr = self.frames.pop()
            self.emit("}")
        elif k == 'while':
            c = self.fresh('c')
            self.emit(f"let {c} = 0")
            self.emit(f"while {c} < 2 {{")
            self.ind += 1
            self.emit(f"{c} += 1")
            self.ind -= 1
            self.block()
            self.emit("}")
        elif k == 'loop':
            self.emit("loop {")
            self.block()
            self.ind += 1
            self.emit("break")
            self.ind -= 1
            self.emit("}")
        elif k == 'blk':
            self.emit("{")
            self.block()
            self.emit("}")
        elif k in ('clo', 'apply', 'twice'):
            g = self.fresh('g')
            self.emit(f"let {g} = || {{")
            self.in_closure += 1
            self.block()
            self.in_closure -= 1
            self.emit("}")
            if k == 'clo':
                self.emit(f"{g}()")
                if self.chance(0.3):
                    self.emit(f"{g}()")
            elif k == 'apply':
                self.emit(f"apply({g})")
            else:
                self.emit(f"twice({g})")
        elif k == 'handle':
            self.handle_stmt()
        elif k == 'scope':
            self.scope_stmt()
        elif k == 'fork':
            a, _, _ = self.closure_body()
            b, _, _ = self.closure_body()
            self.emit(f"fork(|| {a}, || {b})")
        elif k == 'match':
            o = self.pick('o')
            if not o:
                return self.stmt_simple()
            x = self.fresh('x')
            self.emit(f"match {o.name} {{")
            self.ind += 1
            self.emit(f"Some({x}) => {{")
            self.frames.append([])
            self.add(x, 'n')
            self.ind += 1
            for _ in range(self.r.randint(1, 2)):
                self.stmt()
            self.ind -= 1
            self.frames.pop()
            self.emit("}")
            self.emit("None => print(0),")
            self.ind -= 1
            self.emit("}")
        elif k == 'retblk':
            # A block whose value is a reference or a closure that may outlive the block.
            nm = self.fresh('r')
            inner = self.fresh('v')
            kind = r.choice(['r', 'f'])
            if kind == 'r':
                self.emit(f"let {nm} = {{")
                self.ind += 1
                self.emit(f"let {inner} = mk_v()")
                self.emit(r.choice([f"&{inner}[0]", f"first(&{inner})", f"id(&{inner}[1])"]))
                self.ind -= 1
                self.emit("}")
                self.add(nm, 'r')
            else:
                nm = self.fresh('f')
                self.emit(f"let {nm} = {{")
                self.ind += 1
                self.emit(f"let {inner} = mk_v()")
                self.emit(r.choice([f"|| print({inner}.len())", f"|| {inner}.push(1)"] + ([] if 'ff' in OFF else [f"make_reader(&{inner})"])))
                self.ind -= 1
                self.emit("}")
                self.add(nm, 'f')

    def handle_stmt(self):
        r = self.r
        eff = r.choice(['Ask', 'Ask', 'Pick', 'Note', 'Grab', 'Fail'])
        clause_pre = ""
        v = self.pick('v')
        n = self.pick('n')
        rr = self.pick('r')
        extras = ["", "", ""]
        if v:
            extras += [f"{v.name}.push(1); ", f"{v.name}.clear(); ", f"print({v.name}.len()); "]
        if n:
            extras += [f"{n.name} += 1; "]
        if rr:
            extras += [f"print({rr.name}); "]
        clause_pre = r.choice(extras)
        if eff == 'Ask':
            res = r.choice(["resume(5)", "resume(5)", "print(\"no resume\")", "resume(5); print(\"after\")",
                            "resume(1); resume(2)"])
            clause = f"fn ask() {{ {clause_pre}{res} }}"
        elif eff == 'Pick':
            res = r.choice(["resume(true); resume(false)", "resume(true)", "print(\"no\")"])
            clause = f"fn pick() {{ {clause_pre}{res} }}"
        elif eff == 'Note':
            res = r.choice(["resume(())", "print(x); resume(())", "print(\"drop\")"])
            clause = f"fn note(x) {{ {clause_pre}{res} }}"
        elif eff == 'Grab':
            res = r.choice(["resume(r + 1)", "let k = r + 0; resume(k)", "print(\"drop\")"])
            clause = f"fn grab(r) {{ {clause_pre}{res} }}"
        else:
            clause = f"fn fail(m) {{ {clause_pre}print(m) }}"
        self.emit(f"handle {eff} {{ {clause} }} in {{")
        saved = set(self.handled)
        self.handled.add(eff)
        if eff == 'Grab':
            self.handled.add('Ask') if 'Ask' in saved else None
        self.frames.append([])
        self.ind += 1
        self.depth += 1
        for _ in range(r.randint(1, 4)):
            self.stmt()
        if eff == 'Ask' and self.chance(0.5):
            self.emit(r.choice(["print(ask())", "let _ = ask()", "print(with_tx(3))"]))
        if eff == 'Pick' and self.chance(0.6):
            self.emit(f"if pick() {{ print(1) }} else {{ print(2) }}")
        if eff == 'Note' and self.chance(0.6):
            vv = self.pick('v')
            self.emit(f"note_all(&{vv.name})" if vv else "note(2)")
        if eff == 'Grab' and self.chance(0.7):
            e = self.ref_expr()
            if e:
                self.emit(f"print(grab({e}))")
        if eff == 'Fail' and self.chance(0.7):
            self.emit(r.choice(["fail(\"x\")", "maybe_fail(200)", "maybe_fail(1)"]))
        self.depth -= 1
        fr = self.frames.pop()
        self.finish_linears(fr)
        self.ind -= 1
        self.handled = saved
        self.emit("}")

    def scope_stmt(self):
        r = self.r
        s = self.fresh('s')
        self.emit(f"scope {{ {s} =>")
        self.ind += 1
        self.frames.append([])
        saved = self.scope_var
        self.scope_var = s
        for _ in range(r.randint(1, 4)):
            if self.chance(0.6):
                body, _, _ = self.closure_body()
                if self.chance(0.3):
                    t = self.fresh('t')
                    self.emit(f"let {t} = {s}.spawn(|| {body})")
                    if self.chance(0.8):
                        self.stmt_simple()
                        self.emit(f"{t}.join()")
                else:
                    self.emit(f"{s}.spawn(|| {body})")
            else:
                if 'scopedecl' in OFF:
                    self.r.choice([self.mutate, self.use])()
                else:
                    self.stmt_simple()
        self.scope_var = saved
        fr = self.frames.pop()
        self.finish_linears(fr)
        self.ind -= 1
        self.emit("}")

    def extra(self):
        r = self.r
        opts = []
        v = self.pick('v')
        w = self.pick('w')
        if v:
            o = self.fresh('o')
            x = self.fresh('x')
            mid = r.choice(["", f"{v.name}.clear(); ", f"{v.name}.push(1); ", f"grow(&{v.name}); ", ""])
            opts.append(f"let {o} = find(&{v.name}); {mid}match {o} {{ Some({x}) => print({x}), None => print(0) }}")
            opts.append(f"match find(&{v.name}) {{ Some({x}) => {{ {mid}print({x}) }}, None => print(0) }}")
            p = self.fresh('p')
            opts.append(f"let {p} = pair_of(&{v.name}); {mid}let ({x}, _) = {p}; print({x})")
            opts.append(f"let ({x}, _) = pair_of(&{v.name}); {mid}print({x})")
            opts.append(f"each(&{v.name}, |x: &u64| print(x))")
            if r.random() < 0.3:
                opts.append(f"each(&{v.name}, |x: &u64| {{ print(x); {v.name}.push(1) }})")
            opts.append(f"let {x} = &{v.name}[0]; let {p} = ({x}, 2); {mid}let (q{self.n}, _) = {p}; print(q{self.n})")
        if w and not w.attrs.get('isref'):
            e = self.fresh('e')
            mid = r.choice(["", f"{w.name}.add(3); ", f"{w.name}.es.push(mk_e(1)); ", f"{w.name}.score += 1; "])
            opts.append(f"let {e} = {w.name}.top(); {mid}print({e}.hp)")
            opts.append(f"{w.name}.add({w.name}.total())")
            opts.append(f"print({w.name}.total())")
        if 'Fail' in self.handled:
            opts.append(f"with_timeout(5.s) {{ print(1) }}")
        tx = self.pick('tx')
        if tx:
            opts.append(f"print(sum_tx(&{tx.name}))")
        rr = self.pick('r')
        if rr:
            g = self.fresh('g')
            opts.append(f"let {g} = |a: &u64| a; print({g}({rr.name}))")
        if self.in_closure == 0 and self.depth > 0 and r.random() < 0.2:
            opts.append(r.choice(["return", "print(0)"]))
        if not opts:
            return self.decl()
        self.emit(r.choice(opts))

    def stmt_simple(self):
        k = self.r.choice(['decl', 'mutate', 'use', 'use', 'mutate'])
        getattr(self, k)()

    def stmt(self):
        r = self.r
        if self.depth < self.max_depth and self.chance(0.25):
            return self.compound()
        ks = ['decl', 'decl', 'mutate', 'mutate', 'use', 'use', 'use', 'move'] + ([] if 'extra' in OFF else ['extra', 'extra'])
        if getattr(self, 'helpers', None):
            ks += ['call_helper'] * 3
        k = r.choice(ks)
        getattr(self, k)()

    def helper(self, idx):
        """A helper function with a random body and no stated effects."""
        r = self.r
        name = f"h{idx}"
        params = []
        pk = r.sample(['rv', 'rw', 'r', 'f', 'tx', 'v', 'n', 're'], r.randint(1, 3))
        for i, k in enumerate(pk):
            params.append((f"p{i}", k))
        tys = {'rv': '&Vec<u64>', 'rw': '&W', 'r': '&u64', 'f': 'fn()', 'tx': 'Tx', 'v': 'Vec<u64>',
               'n': 'u64', 're': '&E'}
        rets = ['none', 'none', 'u64'] + ([] if 'hfn' in OFF else ['fn'])
        if 'rv' in pk:
            rets.append('refv')
        if 'rw' in pk:
            rets.append('refw')
        ret = r.choice(rets)
        rty = {'none': '', 'u64': ' -> u64', 'fn': ' -> fn()'}.get(ret, ' -> &u64')
        if ret == 'refv':
            pv = [p for p, k in params if k == 'rv'][0]
            rty = f" -> &u64 in {pv}[]"
        if ret == 'refw':
            pw = [p for p, k in params if k == 'rw'][0]
            rty = f" -> &u64 in {pw}.ns[]"
        sig = ", ".join(f"{p}: {tys[k]}" for p, k in params)
        self.lines = [f"fn {name}({sig}){rty} {{"]
        self.ind = 1
        self.frames = [[]]
        self.handled = set()
        for p, k in params:
            if k == 'rw':
                self.add(p, 'w', isref=True)
            else:
                self.add(p, k, param=True)
        for _ in range(r.randint(1, 5)):
            self.stmt()
        self.finish_linears(self.frames[0])
        if ret == 'u64':
            self.emit(self.u64_expr())
        elif ret == 'fn':
            body, _, _ = self.closure_body()
            self.emit(f"|| {body}")
        elif ret == 'refv':
            self.emit(f"&{pv}[0]")
        elif ret == 'refw':
            self.emit(f"&{pw}.ns[0]")
        self.lines.append("}")
        return name, params, ret, "\n".join(self.lines)

    def call_helper(self):
        if not self.helpers:
            return self.use()
        name, params, ret, _ = self.r.choice(self.helpers)
        args = []
        for p, k in params:
            if k == 'rv':
                v = self.pick('v')
                if v:
                    args.append(f"&{v.name}")
                else:
                    rv = self.pick('rv')
                    if not rv:
                        return self.decl()
                    args.append(rv.name)
            elif k == 'rw':
                w = self.pick('w')
                if not w:
                    return self.decl()
                args.append(w.name if w.attrs.get('isref') else f"&{w.name}")
            elif k == 'r':
                e = self.ref_expr()
                if not e:
                    return self.decl()
                args.append(e)
            elif k == 're':
                w = self.pick('w')
                re_ = self.pick('re')
                if re_:
                    args.append(re_.name)
                elif w:
                    args.append(f"&{w.name}.es[0]")
                else:
                    return self.decl()
            elif k == 'f':
                f = self.pick('f')
                if f and self.chance(0.5):
                    args.append(f.name)
                else:
                    body, _, _ = self.closure_body()
                    args.append(f"|| {body}")
            elif k == 'tx':
                tx = self.pick('tx')
                if tx and self.chance(0.7):
                    args.append(tx.name)
                    tx.moved = True
                else:
                    args.append(f"Tx {{ id: {self.n} }}")
            elif k == 'v':
                v = self.pick('v')
                if v and self.chance(0.5):
                    args.append(v.name)
                    v.moved = True
                else:
                    args.append("mk_v()")
            elif k == 'n':
                args.append(self.u64_expr())
        call = f"{name}({', '.join(args)})"
        if ret == 'none':
            self.emit(call)
        elif ret == 'u64':
            nm = self.fresh('n')
            self.emit(f"let {nm} = {call}")
            self.add(nm, 'n')
        elif ret == 'fn':
            nm = self.fresh('f')
            self.emit(f"let {nm} = {call}")
            self.add(nm, 'f')
        else:
            nm = self.fresh('r')
            self.emit(f"let {nm} = {call}")
            self.add(nm, 'r')

    def program(self):
        self.helpers = []
        hl = []
        if 'helpers' not in OFF and self.chance(0.7):
            for i in range(self.r.randint(1, 3)):
                h = self.helper(i)
                self.helpers.append(h)
                hl.append(h[3])
        self.frames = [[]]
        self.handled = set()
        self.lines = ["fn main() {"]
        self.ind = 1
        for _ in range(self.r.randint(4, 12)):
            self.stmt()
        self.finish_linears(self.frames[0])
        self.lines.append("}")
        return PRELUDE + "\n" + "\n\n".join(hl) + "\n\n" + "\n".join(self.lines) + "\n"


def generate(seed, max_depth=3):
    return Gen(seed, max_depth).program()


if __name__ == "__main__":
    import sys
    print(generate(int(sys.argv[1]) if len(sys.argv) > 1 else 1))
