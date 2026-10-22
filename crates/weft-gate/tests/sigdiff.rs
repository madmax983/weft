//! The signature diff (plan stage F6, `weft_gate::sigdiff`).

use weft_gate::ledger::{EntryClass, Ledger};
use weft_gate::sigdiff::{compare, entry_of, FnDiff};
use weft_sema::program::{EffectSig, SigPlace, SigRoot};

/// A `mut` place of parameter `i` with the text `text`.
fn place(i: usize, text: &str) -> SigPlace {
    SigPlace {
        root: SigRoot::Param(i),
        steps: Vec::new(),
        text: text.to_string(),
    }
}

#[test]
fn compare_names_each_part_that_differs() {
    let old = EffectSig {
        muts: vec![place(0, "v")],
        named: std::iter::once("main.Note".to_string()).collect(),
        ..EffectSig::default()
    };
    assert!(compare(&old, &old).is_empty());
    // Only the text of a place differs: a part of its own.
    let text = EffectSig {
        muts: vec![place(0, "w")],
        ..old.clone()
    };
    assert_eq!(compare(&old, &text), vec!["muts text"]);
    // Another root, another effect and `raises`.
    let other = EffectSig {
        muts: vec![place(1, "v")],
        named: std::collections::BTreeSet::default(),
        raises: true,
        ..EffectSig::default()
    };
    assert_eq!(compare(&old, &other), vec!["muts", "named", "raises"]);
}

#[test]
fn a_sig_entry_accepts_the_differences_of_its_parts_and_files() {
    let ledger = Ledger::from_toml(
        r#"
[[entry]]
class = "sig"
parts = ["muts text"]
files = ["a/*.wf"]
reason = "the text of a cut place"
stage = "F6"
"#,
    )
    .expect("a ledger");
    assert_eq!(ledger.entries[0].class, EntryClass::Sig);
    assert_eq!(ledger.entries[0].class.program_class(), None);
    assert!(ledger.entries[0].problem().is_none());
    let diff = |parts: Vec<&'static str>| FnDiff {
        function: "f".to_string(),
        parts,
        old: String::new(),
        ir: String::new(),
    };
    assert_eq!(
        entry_of(&ledger, "a/x.wf", &diff(vec!["muts text"])),
        Some(1)
    );
    assert_eq!(entry_of(&ledger, "a/x.wf", &diff(vec!["muts"])), None);
    assert_eq!(entry_of(&ledger, "b/x.wf", &diff(vec!["muts text"])), None);
    // An entry with no reason has a problem.
    let bare =
        Ledger::from_toml("[[entry]]\nclass = \"sig\"\nfiles = [\"a.wf\"]\n").expect("a ledger");
    assert!(bare.entries[0].problem().is_some());
}

#[test]
fn each_sig_entry_of_the_ledger_is_complete() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(weft_gate::ledger::LEDGER);
    let ledger = Ledger::read(&path).expect("the ledger");
    let sigs: Vec<_> = ledger
        .entries
        .iter()
        .filter(|e| e.class == EntryClass::Sig)
        .collect();
    assert!(!sigs.is_empty());
    for e in sigs {
        assert!(e.problem().is_none(), "{}: {:?}", e.label(), e.problem());
    }
}
