//! Effect names: aliases, bundles and implication.

use std::collections::BTreeSet;
use weft_syntax::diag::Code;

use weft_syntax::ast::EffectPath;
use weft_syntax::diag::Diagnostic;

use crate::program::{EffectId, ItemRef, ModId, Program};

/// The standard effects.
pub const STD_EFFECTS: [&str; 10] = [
    "Async", "Net", "Fs", "Clock", "Rand", "Log", "Blocking", "Fail", "Par", "Io",
];

/// The members of the `io` bundle.
pub const IO: [&str; 7] = ["Async", "Net", "Fs", "Clock", "Rand", "Log", "Blocking"];

/// The first name of the identity of a user effect of the root module
/// (`main.Note`). No dependency can have this name (W0107).
pub const ROOT_PREFIX: &str = "main";

/// Returns true for a standard effect name.
pub fn is_std(name: &str) -> bool {
    STD_EFFECTS.contains(&name)
}

/// Maps a written effect name to canonical names.
///
/// A user effect shadows a standard effect with the same name. Lowercase names
/// are aliases of standard effects. `io` expands to its members.
pub fn canonical(prog: &Program, m: ModId, name: &str) -> Option<Vec<String>> {
    if let Some(ItemRef::Effect(e)) = prog.lookup(m, name) {
        return Some(vec![identity(prog, e)]);
    }
    std_alias(name)
}

/// Resolves a written effect name or path in module `m` to canonical names.
///
/// A path of one name is [`canonical`]. A longer path names modules first, as a
/// type path does: `a.Note`, `util.Note`, `util.sub.Note`. A path into another
/// unit needs a `pub` effect, as a call needs a `pub` function. W0101 is for an
/// unknown or a private effect. Its note gives the paths that name an effect of
/// this name from `m`.
///
/// # Errors
///
/// Returns the W0101 diagnostic if the path names no effect that `m` can name.
pub fn resolve(prog: &Program, m: ModId, path: &EffectPath) -> Result<Vec<String>, Diagnostic> {
    let names = path.names();
    if let [name] = names.as_slice() {
        if let Some(ns) = canonical(prog, m, name) {
            return Ok(ns);
        }
    } else if let Some(e) = resolve_path(prog, m, &names) {
        if visible(prog, m, e) {
            return Ok(vec![identity(prog, e)]);
        }
        return Err(Diagnostic::error(
            Code::W0101,
            format!(
                "effect `{}` is private: it is not `pub` in its package",
                path.text()
            ),
            path.span,
        ));
    }
    let d = Diagnostic::error(
        Code::W0101,
        format!("unknown effect `{}`", path.text()),
        path.span,
    );
    let last = names.last().copied().unwrap_or_default();
    let found: Vec<String> = prog
        .effect_ids()
        .filter(|&e| prog.effects[e].name == last && !prog.effects[e].is_std)
        .filter_map(|e| written(prog, m, &identity(prog, e)))
        .map(|w| format!("`{w}`"))
        .collect();
    Err(match found.as_slice() {
        [] => d,
        [one] => d.note(format!("the effect with this name is written {one} here")),
        _ => d.note(format!(
            "the effects with this name are written {} here",
            found.join(", ")
        )),
    })
}

/// Finds the effect that path `path` names from module `m`: the first name
/// from `m` outward, the other names inside the module before them.
pub fn resolve_path(prog: &Program, m: ModId, path: &[&str]) -> Option<EffectId> {
    let mut module = m;
    for (i, seg) in path.iter().enumerate() {
        let found = if i == 0 {
            prog.lookup(module, seg)
        } else {
            prog.lookup_in(module, seg)
        };
        match found? {
            ItemRef::Mod(s) if i + 1 < path.len() => module = s,
            ItemRef::Effect(e) if i + 1 == path.len() => return Some(e),
            _ => return None,
        }
    }
    None
}

/// Returns true if code in module `m` can name effect `e`: a standard effect,
/// an effect of the same unit, or a `pub` effect.
pub fn visible(prog: &Program, m: ModId, e: EffectId) -> bool {
    let def = &prog.effects[e];
    def.is_std || def.is_pub || prog.mods[def.module].unit == prog.mods[m].unit
}

/// Returns true if code in module `from` can see the user effect with
/// identity `id` (see [`visible`]), also if no path names it there.
pub fn seen(prog: &Program, from: ModId, id: &str) -> bool {
    by_identity(prog, id).is_some_and(|e| visible(prog, from, e))
}

/// Returns the note for user effect `id` that a body cannot name.
///
/// If `hidden`, the body can see the effect, but a nearer name hides the first
/// name of each path to it. Else the effect is private in another package.
pub fn unnamed_note(id: &str, hidden: bool) -> String {
    if hidden {
        format!("`{id}` has no name here: a nearer item hides the first name of each path to it. Rename that item, or state and handle the effect in a module that can name it")
    } else {
        format!("`{id}` is private in its package: code outside the package cannot state or handle it; the package must make it `pub`")
    }
}

/// Returns effect identity `id` as code in module `from` can write it.
///
/// A standard effect has its lowercase alias (`log`). A user effect has the
/// shortest path that names it from `from`: `Note` in its own module, `a.Note`
/// from the parent of module `a`, `util.Note` for a dependency `util`. Returns
/// `None` if `from` cannot name the effect, for example a private effect of
/// another unit.
pub fn written(prog: &Program, from: ModId, id: &str) -> Option<String> {
    if is_std(id) {
        return Some(id.to_lowercase());
    }
    let e = by_identity(prog, id)?;
    if !visible(prog, from, e) {
        return None;
    }
    let def = &prog.effects[e];
    // The names of the modules from the top module of the unit to the module of
    // the effect. The root module has no name.
    let mut mods = Vec::new();
    let mut at = Some(def.module);
    while let Some(m) = at {
        let md = &prog.mods[m];
        if !md.name.is_empty() {
            mods.push(md.name.as_str());
        }
        at = md.parent;
    }
    mods.reverse();
    for i in (0..=mods.len()).rev() {
        let mut path: Vec<&str> = mods[i..].to_vec();
        path.push(def.name.as_str());
        let names = match path.as_slice() {
            [name] => canonical(prog, from, name),
            _ => resolve_path(prog, from, &path).map(|x| vec![identity(prog, x)]),
        };
        if names.is_some_and(|ns| ns == [id]) {
            return Some(path.join("."));
        }
    }
    None
}

/// Maps the alias of a standard effect to canonical names: `net` becomes
/// `Net`, and `io` becomes the members of the bundle.
pub fn std_alias(name: &str) -> Option<Vec<String>> {
    let std = match name {
        "async" => "Async",
        "net" => "Net",
        "fs" => "Fs",
        "clock" => "Clock",
        "rand" => "Rand",
        "log" => "Log",
        "blocking" => "Blocking",
        "fail" => "Fail",
        "par" => "Par",
        "io" | "Io" => return Some(IO.iter().map(|s| (*s).to_string()).collect()),
        _ => return None,
    };
    Some(vec![std.to_string()])
}

/// Returns the effects that a declared effect implies, itself included.
///
/// Net, Fs, Clock and Blocking suspend, so they imply Async.
pub fn implied(name: &str) -> Vec<String> {
    let mut v = vec![name.to_string()];
    if matches!(name, "Net" | "Fs" | "Clock" | "Blocking") {
        v.push("Async".into());
    }
    v
}

/// Closes a set of declared effects under implication.
pub fn close(names: &BTreeSet<String>) -> BTreeSet<String> {
    names.iter().flat_map(|n| implied(n)).collect()
}

/// Returns the identity of effect `e` in the facts and the signatures.
///
/// A standard effect keeps its name. A user effect gets its module path and its
/// name (`main.Log`, `json.parse.Log`). So a user effect can have the name of a
/// standard effect, but not its identity.
pub fn identity(prog: &Program, e: EffectId) -> String {
    let def = &prog.effects[e];
    if def.is_std {
        return def.name.clone();
    }
    let mut path = vec![def.name.as_str()];
    let mut at = Some(def.module);
    while let Some(m) = at {
        let md = &prog.mods[m];
        match (md.parent, md.name.as_str()) {
            (None, "") => path.push(ROOT_PREFIX),
            (_, name) => path.push(name),
        }
        at = md.parent;
    }
    path.reverse();
    path.join(".")
}

/// Finds an effect by its identity. After item collection this is a lookup in
/// `Program::effect_index`; during item collection it is a search.
pub fn by_identity(prog: &Program, id: &str) -> Option<EffectId> {
    if let Some(index) = &prog.effect_index {
        return index.get(id).copied();
    }
    let name = shown(id);
    prog.effect_ids()
        .filter(|&e| prog.effects[e].name == name)
        .find(|&e| identity(prog, e) == id)
}

/// Returns the name of an effect identity as the source writes it: `main.Log`
/// is `Log`.
pub fn shown(id: &str) -> &str {
    id.rsplit('.').next().unwrap_or(id)
}

/// Returns an effect identity as a signature writes it.
///
/// A standard effect has its lowercase alias (`Log` is `log`). A user effect has
/// its name (`main.Log2` is `Log2`). A bare effect name gives the same text as
/// its identity.
pub fn in_signature(id: &str) -> String {
    if is_std(id) {
        id.to_lowercase()
    } else {
        shown(id).to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn closure_adds_async() {
        let s: BTreeSet<String> = ["Net".to_string(), "Log".to_string()].into_iter().collect();
        let c = close(&s);
        assert!(c.contains("Async") && c.contains("Net") && c.contains("Log"));
        assert!(is_std("Par"));
        assert!(!is_std("Choice"));
        assert_eq!(in_signature("Log"), "log");
        assert_eq!(in_signature("Log2"), "Log2");
        assert_eq!(in_signature("main.Log2"), "Log2");
        assert_eq!(in_signature("main.Log"), "Log");
        assert_eq!(in_signature("json.sub.Note"), "Note");
    }
}
