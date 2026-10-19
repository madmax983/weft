//! Effect names: aliases, bundles and implication.

use std::collections::BTreeSet;

use crate::program::{EffectId, ItemRef, ModId, Program};

/// The standard effects.
pub const STD_EFFECTS: [&str; 10] = [
    "Async", "Net", "Fs", "Clock", "Rand", "Log", "Blocking", "Fail", "Par", "Io",
];

/// The members of the `io` bundle.
pub const IO: [&str; 7] = ["Async", "Net", "Fs", "Clock", "Rand", "Log", "Blocking"];

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
            (None, "") => path.push("main"),
            (_, name) => path.push(name),
        }
        at = md.parent;
    }
    path.reverse();
    path.join(".")
}

/// Finds an effect by its identity.
pub fn by_identity(prog: &Program, id: &str) -> Option<EffectId> {
    let name = shown(id);
    (0..prog.effects.len())
        .filter(|&e| prog.effects[e].name == name)
        .find(|&e| identity(prog, e) == id)
}

/// Returns the name of an effect identity as the source writes it: `main.Log`
/// is `Log`.
pub fn shown(id: &str) -> &str {
    id.rsplit('.').next().unwrap_or(id)
}

/// Returns an effect identity as a signature writes it: a standard effect by its
/// lowercase alias (`Log` is `log`), a user effect by its name.
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
    }
}
