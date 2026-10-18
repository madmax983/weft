//! Effect names: aliases, bundles and implication.

use std::collections::BTreeSet;

use crate::program::{ItemRef, ModId, Program};

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
        return Some(vec![prog.effects[e].name.clone()]);
    }
    std_alias(name)
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
