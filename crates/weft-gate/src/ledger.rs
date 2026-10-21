//! The ledger of the gate: `tests/gate/ledger.toml` (plan §2.5).
//!
//! The ledger accepts a group of programs of one class with a reason. Each
//! [`Entry`] names its programs with paths or globs ([`glob_match`]). The rules
//! of the report (`crate::report`) say which classes need an entry and which
//! fields the entry must have ([`Entry::problem`]).

use serde::Deserialize;

use crate::classify::Class;
use crate::Error;

/// The ledger, relative to the repository.
pub const LEDGER: &str = "tests/gate/ledger.toml";

/// The class of a ledger entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum EntryClass {
    /// An `open` program whose finding has the verdict "stays" in `ir §10`.
    Open,
    /// An `open` program that the ship rule accepts, with an issue.
    Edge,
    /// An `open` program that the old pipeline also accepts today (stage G6).
    OpenOld,
    /// A `new-fp` program of the probes.
    NewFp,
    /// A `lost-clean` program, signed by a reviewer.
    LostClean,
    /// A `moved` program.
    Moved,
    /// A `changed` program.
    Changed,
    /// A difference of the engine differential (`crate::engines`), not a
    /// class of the gate.
    Engine,
}

impl EntryClass {
    /// The name in the ledger.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Open => "open",
            Self::Edge => "edge",
            Self::OpenOld => "open-old",
            Self::NewFp => "new-fp",
            Self::LostClean => "lost-clean",
            Self::Moved => "moved",
            Self::Changed => "changed",
            Self::Engine => "engine",
        }
    }

    /// The class of the programs that an entry of this class accepts in the
    /// gate. An `engine` entry accepts no program of the gate: it accepts a
    /// difference of the engine differential.
    pub const fn program_class(self) -> Option<Class> {
        match self {
            Self::Open | Self::Edge | Self::OpenOld => Some(Class::Open),
            Self::NewFp => Some(Class::NewFp),
            Self::LostClean => Some(Class::LostClean),
            Self::Moved => Some(Class::Moved),
            Self::Changed => Some(Class::Changed),
            Self::Engine => None,
        }
    }
}

/// Why the `ir` pipeline rejects a `new-fp` program.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ReasonClass {
    /// A rule of ADR 0012 is stricter than the old rule.
    Stricter,
    /// The `ir` pipeline is less precise. The entry needs an issue.
    Precision,
}

/// One entry of the ledger.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Entry {
    /// The class.
    pub class: EntryClass,
    /// The paths or globs of the programs, relative to the repository.
    pub files: Vec<String>,
    /// The finding id, for example `V069`.
    #[serde(default)]
    pub finding: Option<String>,
    /// The verdict of the finding in `ir §10` (class `open`: "stays").
    #[serde(default)]
    pub verdict: Option<String>,
    /// The issue number (class `edge`, and `new-fp` with a precision loss).
    #[serde(default)]
    pub issue: Option<u64>,
    /// Why the `ir` pipeline rejects the program (class `new-fp`).
    #[serde(default)]
    pub reason_class: Option<ReasonClass>,
    /// The codes that the entry accepts (classes `moved` and `changed`).
    /// Empty means each code.
    #[serde(default)]
    pub codes: Vec<String>,
    /// The reason.
    #[serde(default)]
    pub reason: Option<String>,
    /// The reviewer (class `lost-clean`): a person or a review agent that is
    /// not the author of the stage.
    #[serde(default)]
    pub signed_by: Option<String>,
    /// The stage that added the entry.
    #[serde(default)]
    pub stage: Option<String>,
    /// The class of the difference (class `engine`): a name of
    /// `crate::engines::Kind`.
    #[serde(default)]
    pub difference: Option<String>,
    /// `"rejects"` (class `engine`): the entry is a rule for each program
    /// that the checker rejects. With no `checker`, the entry must name each
    /// program with a path (no glob).
    #[serde(default)]
    pub checker: Option<String>,
}

/// True if the text is there and is not empty.
fn given(text: Option<&String>) -> bool {
    text.is_some_and(|t| !t.trim().is_empty())
}

impl Entry {
    /// True if a pattern of [`Entry::files`] matches one of `paths`.
    pub fn matches<S: AsRef<str>>(&self, paths: &[S]) -> bool {
        self.files
            .iter()
            .any(|f| paths.iter().any(|p| glob_match(f, p.as_ref())))
    }

    /// True if the entry accepts each code of `codes`.
    pub fn accepts_codes<S: AsRef<str>>(&self, codes: &[S]) -> bool {
        self.codes.is_empty()
            || codes
                .iter()
                .all(|c| self.codes.iter().any(|k| k == c.as_ref()))
    }

    /// The fields that the entry needs and does not have, or `None` if the
    /// entry is complete.
    pub fn problem(&self) -> Option<String> {
        let reason = given(self.reason.as_ref());
        let finding = given(self.finding.as_ref());
        let text = match self.class {
            EntryClass::Open if !finding => "a `finding`",
            EntryClass::Open if self.verdict.as_deref().map(str::trim) != Some("stays") => {
                "`verdict = \"stays\"`"
            }
            EntryClass::Edge if self.issue.is_none() => "an `issue`",
            EntryClass::OpenOld if !finding => "a `finding` (or \"unclassified\")",
            EntryClass::NewFp => match self.reason_class {
                None => "a `reason_class` (\"stricter\" or \"precision\")",
                Some(ReasonClass::Precision) if self.issue.is_none() => {
                    "an `issue` for a precision loss"
                }
                Some(_) => return None,
            },
            EntryClass::LostClean if !finding && !reason => "a `finding` or a `reason`",
            EntryClass::LostClean if !given(self.signed_by.as_ref()) => {
                "`signed_by` (a reviewer that is not the author of the stage)"
            }
            EntryClass::Moved | EntryClass::Changed | EntryClass::Engine if !reason => "a `reason`",
            EntryClass::Engine if !given(self.difference.as_ref()) => {
                "a `difference` (the class of the difference)"
            }
            EntryClass::Engine
                if self.checker.is_some() && self.checker.as_deref() != Some("rejects") =>
            {
                "`checker = \"rejects\"` or no `checker`"
            }
            EntryClass::Engine
                if self.checker.is_none() && self.files.iter().any(|f| f.contains(['*', '?'])) =>
            {
                "a path with no glob for each program, or `checker = \"rejects\"`"
            }
            _ => return None,
        };
        Some(format!("the entry needs {text}"))
    }

    /// A short name of the entry for a message: its class and its files.
    pub fn label(&self) -> String {
        format!("{} [{}]", self.class.name(), self.files.join(", "))
    }
}

/// The ledger: its entries in the order of the file.
#[derive(Clone, Debug, Default, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Ledger {
    /// The entries (`[[entry]]`).
    #[serde(default, rename = "entry")]
    pub entries: Vec<Entry>,
}

impl Ledger {
    /// Reads the text of a ledger.
    ///
    /// # Errors
    ///
    /// Returns [`Error::Ledger`] if the text is not TOML, if an entry has an
    /// unknown field or class, or if an entry has no file or an empty pattern.
    pub fn from_toml(text: &str) -> Result<Self, Error> {
        let ledger: Self = toml::from_str(text).map_err(|e| Error::Ledger(e.to_string()))?;
        for (i, e) in ledger.entries.iter().enumerate() {
            if e.files.is_empty() || e.files.iter().any(|f| f.trim().is_empty()) {
                return Err(Error::Ledger(format!(
                    "entry {} ({}) needs one or more files, and no file can be empty",
                    i + 1,
                    e.class.name()
                )));
            }
        }
        Ok(ledger)
    }

    /// Reads the ledger file `path`. A file that does not exist gives an
    /// empty ledger.
    ///
    /// # Errors
    ///
    /// Returns [`Error::Io`] if the file cannot be read, and the errors of
    /// [`Ledger::from_toml`].
    pub fn read(path: &std::path::Path) -> Result<Self, Error> {
        match std::fs::read_to_string(path) {
            Ok(text) => Self::from_toml(&text).map_err(|e| match e {
                Error::Ledger(m) => Error::Ledger(format!("{}: {m}", path.display())),
                other => other,
            }),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(Self::default()),
            Err(e) => Err(Error::io(path, e)),
        }
    }
}

/// True if the glob `pattern` matches all of `path`.
///
/// `*` matches a sequence of characters with no `/`. `?` matches one character
/// that is not `/`. `**/` matches zero or more directories, and `**` at the
/// end matches all the rest. Each other character matches itself.
pub fn glob_match(pattern: &str, path: &str) -> bool {
    let p: Vec<char> = pattern.chars().collect();
    let s: Vec<char> = path.chars().collect();
    glob(&p, &s)
}

fn glob(p: &[char], s: &[char]) -> bool {
    match p {
        [] => s.is_empty(),
        ['*', '*', '/', rest @ ..] => {
            glob(rest, s)
                || s.iter()
                    .enumerate()
                    .any(|(i, c)| *c == '/' && s.get(i + 1..).is_some_and(|t| glob(rest, t)))
        }
        ['*', '*', rest @ ..] => (0..=s.len()).any(|i| s.get(i..).is_some_and(|t| glob(rest, t))),
        ['*', rest @ ..] => {
            let end = s.iter().position(|c| *c == '/').unwrap_or(s.len());
            (0..=end).any(|i| s.get(i..).is_some_and(|t| glob(rest, t)))
        }
        ['?', rest @ ..] => match s {
            [c, t @ ..] => *c != '/' && glob(rest, t),
            [] => false,
        },
        [c, rest @ ..] => match s {
            [d, t @ ..] => c == d && glob(rest, t),
            [] => false,
        },
    }
}
