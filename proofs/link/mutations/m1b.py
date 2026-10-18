# DESC: As m1, and the lemmas of `places.rs` that need the unstable step change too.
import sys; sys.path.insert(0, sys.argv[0].rsplit('/',1)[0]); from _lib import sub
d=sys.argv[1]; f="crates/weft-verified/src/places.rs"
sub(d,f,"m.len() < p.len() && spec_may_prefix(m, p) && spec_crosses_unstable(m.len() as int, p)\n}","m.len() < p.len() && spec_may_prefix(m, p)\n}")
sub(d,f,"m.len() < p.len() && may_prefix(m, p) && crosses_unstable(m.len(), p)\n}","m.len() < p.len() && may_prefix(m, p)\n}")
# drop the lemma that states rule 4, and the unstable witnesses in two lemmas
sub(d,f,"""    requires
        forall|i: int| m.len() <= i < p.len() ==> !(#[trigger] p[i]).unstable,
    ensures
        !spec_invalidates(m, p),
""","""    requires
        forall|i: int| m.len() <= i < p.len() ==> !(#[trigger] p[i]).unstable,
    ensures
        true,
""")
sub(d,f,"    let k = choose|k: int| (m + s).len() <= k < p.len() && #[trigger] p[k].unstable;\n    assert(m.len() <= k);\n","")
sub(d,f,"    let k = choose|k: int| m.len() <= k < p.len() && #[trigger] p[k].unstable;\n    assert(d.len() <= k);\n","")
