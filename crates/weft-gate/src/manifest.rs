//! The manifest of the gate: the programs of tier 1 and tier 2 (plan §2.1).
//!
//! A manifest has one [`Entry`] for each distinct program. A program is a `.wf` file
//! or a package (a directory with `weft.toml`). The SHA-256 of the text identifies a
//! program. The first path in the order of the roots, and then in sorted order, is the
//! path of the entry. The other paths with the same text are in [`Entry::others`].

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};
use weft_syntax::lexer::{lex, TokenKind};

use crate::Error;

/// The path components that the exclusion rule of tier 2 skips: copies of the
/// repository. The repository sets of tier 1 have the current versions.
pub const EXCLUDED_COMPONENTS: [&str; 5] = ["target", "crates", "tests", "std", "examples"];

/// The default root of tier 2 when `WEFT_GATE_PROBES` is not set.
///
/// It is the scratch directory of the session that made the plan. It can go away;
/// then use the unpacked archive (`tests/gate/probes-tier2.sha256` names its hash).
pub const DEFAULT_PROBES: &str =
    "/tmp/claude-0/-home-user-weft/da0e5bf6-1701-54dd-be37-5c174a731219/scratchpad";

/// The header line of the manifest text.
pub const HEADER: &str = "hash\tpath\tset\tmode\thas_main\thas_tests\tother_paths";

/// How the gate checks and runs a program.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Mode {
    /// One `.wf` file.
    File,
    /// A directory with `weft.toml` (package mode).
    Package,
}

impl Mode {
    /// The name in the manifest text.
    pub const fn name(self) -> &'static str {
        match self {
            Self::File => "file",
            Self::Package => "package",
        }
    }
}

/// Which files of a root directory the manifest reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Scope {
    /// Only the `.wf` files directly in the directory.
    Files,
    /// Each `.wf` file and each package below the directory.
    Tree,
}

/// A root directory of a set of programs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Root {
    /// The name of the set (the `set` column).
    pub set: String,
    /// The directory, relative to the base directory. Empty means the base.
    pub dir: PathBuf,
    /// Which files the manifest reads.
    pub scope: Scope,
}

impl Root {
    fn new(set: &str, dir: &str, scope: Scope) -> Self {
        Self {
            set: set.to_string(),
            dir: PathBuf::from(dir),
            scope,
        }
    }

    /// Returns true if the manifest path `path` (with `/`) is in this root.
    pub fn holds(&self, path: &str) -> bool {
        let dir = slash_path(&self.dir);
        let rest = if dir.is_empty() {
            Some(path)
        } else {
            path.strip_prefix(dir.as_str())
                .and_then(|r| r.strip_prefix('/'))
        };
        match (rest, self.scope) {
            (None, _) => path == dir && self.scope == Scope::Tree,
            (Some(r), Scope::Files) => !r.is_empty() && !r.contains('/'),
            (Some(r), Scope::Tree) => !r.is_empty(),
        }
    }
}

/// The group of a tier-2 root (plan §2.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Group {
    /// A report root of rounds 1 to 3 and of the IR design.
    Report,
    /// A stage root (the stage verifiers and the open lists).
    Stage,
}

/// A tier-2 root and its group.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TierRoot {
    /// The group.
    pub group: Group,
    /// The root.
    pub root: Root,
}

/// The options of [`build`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Options {
    /// Apply the exclusion rule of tier 2: skip each file below a directory with a
    /// `Cargo.toml`, and each file with a path component in [`EXCLUDED_COMPONENTS`].
    pub exclude_copies: bool,
}

/// One distinct program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    /// The SHA-256 of the text, in lower-case hex. For a package, the hash of
    /// [`package_files`] and their texts (see [`package_hash`]).
    pub hash: String,
    /// The first path, relative to the base, with `/`.
    pub path: String,
    /// The set of the root that holds `path`.
    pub set: String,
    /// File or package.
    pub mode: Mode,
    /// True if the root module has `fn main`.
    pub has_main: bool,
    /// True if a module has a `test "name" { ... }` block.
    pub has_tests: bool,
    /// The other paths with the same hash, in order.
    pub others: Vec<String>,
}

/// The list of distinct programs.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Manifest {
    /// The entries, in the order of the roots and then of the paths.
    pub entries: Vec<Entry>,
    /// The root directories that do not exist, with `/`.
    pub missing: Vec<String>,
}

/// The roots of tier 1: the repository sets of plan §2.1.
pub fn tier1_roots() -> Vec<Root> {
    vec![
        Root::new("corpus", "tests/programs", Scope::Files),
        Root::new("interp", "crates/weft-interp/tests/programs", Scope::Files),
        Root::new("examples", "examples", Scope::Tree),
        Root::new("packages", "tests/packages", Scope::Tree),
        Root::new("probes", "tests/gate/probes", Scope::Tree),
    ]
}

/// The roots of tier 2, relative to `WEFT_GATE_PROBES`: the report roots, the stage
/// roots, and the `.wf` files at the top (set `top`), in this order.
pub fn tier2_roots() -> Vec<TierRoot> {
    let report = ["redteam", "specreview", "r2", "r3", "ir"];
    let stage = [
        "verify", "fix", "s2", "s2fix", "edge", "edgefix", "partb", "s5", "s5r", "s1fix", "p",
        "core", "backup",
    ];
    let mut out = Vec::new();
    for d in report {
        out.push(TierRoot {
            group: Group::Report,
            root: Root::new(d, d, Scope::Tree),
        });
    }
    for d in stage {
        out.push(TierRoot {
            group: Group::Stage,
            root: Root::new(d, d, Scope::Tree),
        });
    }
    out.push(TierRoot {
        group: Group::Stage,
        root: Root::new("top", "", Scope::Files),
    });
    out
}

/// A program that the walk found, before the dedupe.
struct Found {
    rel: String,
    full: PathBuf,
    mode: Mode,
}

/// Lists the programs below `base` in `roots`.
///
/// The roots come in priority order: if two roots hold the same text, the entry
/// keeps the path of the earlier root. In one root, the first path in sorted order
/// stays.
pub fn build(base: &Path, roots: &[Root], opts: Options) -> Result<Manifest, Error> {
    let mut manifest = Manifest::default();
    let mut by_hash: HashMap<String, usize> = HashMap::new();
    let mut seen: HashSet<String> = HashSet::new();
    for root in roots {
        let full = base.join(&root.dir);
        if !is_real_dir(&full) {
            manifest.missing.push(slash_path(&root.dir));
            continue;
        }
        if opts.exclude_copies && root_is_excluded(base, &root.dir) {
            continue;
        }
        let mut found = Vec::new();
        match root.scope {
            Scope::Files => top_files(&full, &root.dir, &mut found)?,
            Scope::Tree => walk(&full, &root.dir, opts, &mut found)?,
        }
        found.sort_by(|a, b| a.rel.cmp(&b.rel));
        for f in found {
            if !seen.insert(f.rel.clone()) {
                continue;
            }
            let (hash, has_main, has_tests) = match f.mode {
                Mode::File => {
                    let bytes = fs::read(&f.full).map_err(|e| Error::io(&f.full, e))?;
                    let (m, t) = scan(&String::from_utf8_lossy(&bytes));
                    (hex(&Sha256::digest(&bytes)), m, t)
                }
                Mode::Package => {
                    let (m, t) = package_flags(&f.full)?;
                    (package_hash(&f.full)?, m, t)
                }
            };
            if let Some(&i) = by_hash.get(&hash) {
                if let Some(e) = manifest.entries.get_mut(i) {
                    e.others.push(f.rel);
                }
                continue;
            }
            by_hash.insert(hash.clone(), manifest.entries.len());
            manifest.entries.push(Entry {
                hash,
                path: f.rel,
                set: root.set.clone(),
                mode: f.mode,
                has_main,
                has_tests,
                others: Vec::new(),
            });
        }
    }
    Ok(manifest)
}

/// Lists the files of the package in `dir`: each `weft.toml` and each `.wf` file
/// below it, relative to `dir`, with `/`, in sorted order. The list skips symbolic
/// links and directories named `target`.
pub fn package_files(dir: &Path) -> Result<Vec<String>, Error> {
    fn go(dir: &Path, rel: &str, out: &mut Vec<String>) -> Result<(), Error> {
        for (name, kind) in read_dir_sorted(dir)? {
            let child = join_rel(rel, &name);
            match kind {
                Kind::Dir if name != "target" => go(&dir.join(&name), &child, out)?,
                Kind::File if name == "weft.toml" || is_wf(&name) => out.push(child),
                _ => {}
            }
        }
        Ok(())
    }
    let mut out = Vec::new();
    go(dir, "", &mut out)?;
    out.sort();
    Ok(out)
}

/// The hash of the package in `dir`: the SHA-256 of, for each file of
/// [`package_files`] in order, the path, a line feed, the length in bytes in
/// decimal, a line feed, and the bytes.
pub fn package_hash(dir: &Path) -> Result<String, Error> {
    let mut h = Sha256::new();
    for rel in package_files(dir)? {
        let path = dir.join(&rel);
        let bytes = fs::read(&path).map_err(|e| Error::io(&path, e))?;
        h.update(format!("{rel}\n{}\n", bytes.len()).as_bytes());
        h.update(&bytes);
    }
    Ok(hex(&h.finalize()))
}

/// The flags of a package: its root module is `src/main.wf`, else `src/lib.wf`.
fn package_flags(dir: &Path) -> Result<(bool, bool), Error> {
    for root in ["src/main.wf", "src/lib.wf"] {
        let path = dir.join(root);
        if path.is_file() {
            let bytes = fs::read(&path).map_err(|e| Error::io(&path, e))?;
            return Ok(scan(&String::from_utf8_lossy(&bytes)));
        }
    }
    Ok((false, false))
}

/// Finds `fn main` in the root module and `test "name" {` in any module.
///
/// The scan uses the tokens, not the syntax tree, so that a deep or a broken probe
/// cannot stop the manifest. A text that does not lex has neither.
pub fn scan(text: &str) -> (bool, bool) {
    let Ok(tokens) = lex(text) else {
        return (false, false);
    };
    let mut depth = 0usize;
    let mut has_main = false;
    let mut has_tests = false;
    for (i, t) in tokens.iter().enumerate() {
        let next = |k: usize| tokens.get(i + k).map(|t| &t.kind);
        match &t.kind {
            TokenKind::LBrace => depth += 1,
            TokenKind::RBrace => depth = depth.saturating_sub(1),
            TokenKind::Fn
                if depth == 0 && matches!(next(1), Some(TokenKind::Name(n)) if n == "main") =>
            {
                has_main = true;
            }
            TokenKind::Name(n)
                if n == "test"
                    && matches!(next(1), Some(TokenKind::Str(_)))
                    && matches!(next(2), Some(TokenKind::LBrace)) =>
            {
                has_tests = true;
            }
            _ => {}
        }
    }
    (has_main, has_tests)
}

impl Manifest {
    /// The number of paths: the entries and their other paths.
    pub fn path_count(&self) -> usize {
        self.entries.iter().map(|e| 1 + e.others.len()).sum()
    }

    /// Each path of the manifest, with the entry that holds it.
    pub fn all_paths(&self) -> impl Iterator<Item = (&Entry, &str)> {
        self.entries.iter().flat_map(|e| {
            std::iter::once(e.path.as_str())
                .chain(e.others.iter().map(String::as_str))
                .map(move |p| (e, p))
        })
    }

    /// The manifest text: [`HEADER`], then one line for each entry. A field escapes
    /// `\`, tab, line feed, carriage return and `;` with `\`. The other paths are
    /// separated by `;`.
    pub fn to_tsv(&self) -> String {
        let mut out = String::new();
        out.push_str(HEADER);
        out.push('\n');
        for e in &self.entries {
            let others: Vec<String> = e.others.iter().map(|p| escape(p)).collect();
            let _ = writeln!(
                out,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}",
                e.hash,
                escape(&e.path),
                escape(&e.set),
                e.mode.name(),
                u8::from(e.has_main),
                u8::from(e.has_tests),
                others.join(";"),
            );
        }
        out
    }

    /// Reads a manifest text that [`Manifest::to_tsv`] wrote.
    pub fn from_tsv(text: &str) -> Result<Self, Error> {
        let mut lines = text.lines().enumerate();
        match lines.next() {
            Some((_, h)) if h == HEADER => {}
            _ => return Err(syntax(1, "the header line is not correct")),
        }
        let mut entries = Vec::new();
        for (i, line) in lines {
            let n = i + 1;
            if line.is_empty() {
                continue;
            }
            let f: Vec<&str> = line.split('\t').collect();
            let [hash, path, set, mode, main, tests, others] = f.as_slice() else {
                return Err(syntax(n, "a line must have 7 fields"));
            };
            let mode = match *mode {
                "file" => Mode::File,
                "package" => Mode::Package,
                m => return Err(syntax(n, &format!("unknown mode `{m}`"))),
            };
            entries.push(Entry {
                hash: (*hash).to_string(),
                path: unescape(path, n)?,
                set: unescape(set, n)?,
                mode,
                has_main: flag(main, n)?,
                has_tests: flag(tests, n)?,
                others: split_escaped(others)
                    .into_iter()
                    .map(|p| unescape(p, n))
                    .collect::<Result<_, _>>()?,
            });
        }
        Ok(Self {
            entries,
            missing: Vec::new(),
        })
    }
}

fn syntax(line: usize, message: &str) -> Error {
    Error::Syntax {
        line,
        message: message.to_string(),
    }
}

fn flag(s: &str, line: usize) -> Result<bool, Error> {
    match s {
        "1" => Ok(true),
        "0" => Ok(false),
        _ => Err(syntax(line, &format!("a flag must be 0 or 1, not `{s}`"))),
    }
}

fn escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '\t' => out.push_str("\\t"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            ';' => out.push_str("\\;"),
            c => out.push(c),
        }
    }
    out
}

fn unescape(s: &str, line: usize) -> Result<String, Error> {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('\\') => out.push('\\'),
            Some('t') => out.push('\t'),
            Some('n') => out.push('\n'),
            Some('r') => out.push('\r'),
            Some(';') => out.push(';'),
            _ => return Err(syntax(line, "a field has a bad escape")),
        }
    }
    Ok(out)
}

/// Splits at each `;` that has no `\` before it. An empty text gives no parts.
fn split_escaped(s: &str) -> Vec<&str> {
    if s.is_empty() {
        return Vec::new();
    }
    let mut parts = Vec::new();
    let mut start = 0;
    let mut escaped = false;
    for (i, c) in s.char_indices() {
        match c {
            _ if escaped => escaped = false,
            '\\' => escaped = true,
            ';' => {
                parts.push(&s[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    parts.push(&s[start..]);
    parts
}

/// Writes `bytes` in lower-case hex.
pub fn hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(out, "{b:02x}");
    }
    out
}

/// The kind of a directory entry. A symbolic link is [`Kind::Other`].
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    File,
    Dir,
    Other,
}

/// Reads a directory. The names are in sorted order; a name that is not UTF-8 is
/// converted with replacement characters.
fn read_dir_sorted(dir: &Path) -> Result<Vec<(String, Kind)>, Error> {
    let rd = fs::read_dir(dir).map_err(|e| Error::io(dir, e))?;
    let mut out = Vec::new();
    for ent in rd {
        let ent = ent.map_err(|e| Error::io(dir, e))?;
        let ft = ent.file_type().map_err(|e| Error::io(ent.path(), e))?;
        let kind = if ft.is_file() {
            Kind::File
        } else if ft.is_dir() {
            Kind::Dir
        } else {
            Kind::Other
        };
        out.push((ent.file_name().to_string_lossy().into_owned(), kind));
    }
    out.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(out)
}

fn is_real_dir(path: &Path) -> bool {
    fs::symlink_metadata(path).is_ok_and(|m| m.is_dir())
}

fn is_wf(name: &str) -> bool {
    Path::new(name).extension().is_some_and(|e| e == "wf")
}

fn join_rel(rel: &str, name: &str) -> String {
    if rel.is_empty() {
        name.to_string()
    } else {
        format!("{rel}/{name}")
    }
}

fn slash_path(p: &Path) -> String {
    p.components()
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join("/")
}

/// Applies the exclusion rule to the root directory `dir` itself.
fn root_is_excluded(base: &Path, dir: &Path) -> bool {
    let mut at = base.to_path_buf();
    if at.join("Cargo.toml").is_file() {
        return true;
    }
    for c in dir.components() {
        let name = c.as_os_str().to_string_lossy();
        if EXCLUDED_COMPONENTS.contains(&name.as_ref()) {
            return true;
        }
        at.push(c);
        if at.join("Cargo.toml").is_file() {
            return true;
        }
    }
    false
}

fn top_files(full: &Path, dir: &Path, out: &mut Vec<Found>) -> Result<(), Error> {
    let rel = slash_path(dir);
    for (name, kind) in read_dir_sorted(full)? {
        if kind == Kind::File && is_wf(&name) {
            out.push(Found {
                rel: join_rel(&rel, &name),
                full: full.join(&name),
                mode: Mode::File,
            });
        }
    }
    Ok(())
}

fn walk(full: &Path, dir: &Path, opts: Options, out: &mut Vec<Found>) -> Result<(), Error> {
    fn go(full: &Path, rel: &str, opts: Options, out: &mut Vec<Found>) -> Result<(), Error> {
        if full.join("weft.toml").is_file() {
            out.push(Found {
                rel: rel.to_string(),
                full: full.to_path_buf(),
                mode: Mode::Package,
            });
            return Ok(());
        }
        if opts.exclude_copies && full.join("Cargo.toml").is_file() {
            return Ok(());
        }
        for (name, kind) in read_dir_sorted(full)? {
            let child = join_rel(rel, &name);
            match kind {
                Kind::Dir => {
                    if !(opts.exclude_copies && EXCLUDED_COMPONENTS.contains(&name.as_str())) {
                        go(&full.join(&name), &child, opts, out)?;
                    }
                }
                Kind::File if is_wf(&name) => out.push(Found {
                    rel: child,
                    full: full.join(&name),
                    mode: Mode::File,
                }),
                _ => {}
            }
        }
        Ok(())
    }
    go(full, &slash_path(dir), opts, out)
}
