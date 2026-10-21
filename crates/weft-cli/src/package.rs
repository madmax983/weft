//! Packages: `weft.toml`, dependencies and their authority.
//!
//! A project grants each dependency a set of standard effects. The code of
//! the dependency must stay inside that set. This applies to the row of each
//! function, also a private one: the root can call only a `pub` function
//! (W0101), but a public function or a returned closure can run a private
//! one. It also applies to the effects that its body infers beyond its
//! signature. It also applies to each effect that a closure
//! in a body performs, because the closure can leave the dependency as a
//! value. Only the standard effects count. A user effect of a dependency
//! needs no authority, because the caller must handle it. When the project
//! loads a JSON parser that asks for `Net`, W0901 rejects it ("install
//! time").

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use weft_syntax::diag::Code;

use anyhow::{bail, Context, Result};
use serde::Deserialize;
use weft_sema::{effects, Analysis, Unit};
use weft_syntax::diag::{Diagnostic, ROOT_UNIT};
use weft_syntax::{parse_file, SourceFile};

/// The kind of package.
#[derive(Clone, Copy, Debug, Default, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum Kind {
    /// A binary: it may install root handlers and enable the GC tier.
    #[default]
    Bin,
    /// A library.
    Lib,
}

/// The runtime profile.
#[derive(Clone, Copy, Debug, Default, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum Runtime {
    /// `std.rt` handles the standard effects.
    #[default]
    Std,
    /// The embedded profile: `main` installs its own executor.
    None,
}

/// The `[package]` table.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PackageTable {
    /// The package name.
    pub name: String,
    /// The package kind.
    #[serde(default)]
    pub kind: Kind,
    /// The GC tier switch (Phase 3). Only a binary may set it.
    #[serde(default)]
    pub gc: bool,
    /// The runtime profile.
    #[serde(default)]
    pub runtime: Runtime,
}

/// A `[dependencies.NAME]` table.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DepTable {
    /// The path of the dependency, relative to the manifest.
    pub path: String,
    /// The effects that the project grants to the dependency.
    #[serde(default)]
    pub authority: Vec<String>,
}

/// A parsed `weft.toml`.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Manifest {
    /// The package table.
    pub package: PackageTable,
    /// The dependencies by name.
    #[serde(default)]
    pub dependencies: std::collections::BTreeMap<String, DepTable>,
}

impl Manifest {
    /// Reads a manifest.
    pub fn read(path: &Path) -> Result<Self> {
        let text =
            fs::read_to_string(path).with_context(|| format!("cannot read {}", path.display()))?;
        toml::from_str(&text).with_context(|| format!("{} is not a valid manifest", path.display()))
    }
}

/// A dependency as loaded.
#[derive(Clone, Debug)]
pub struct Dependency {
    /// The module name.
    pub name: String,
    /// The unit index.
    pub unit: usize,
    /// The granted effects, canonical and closed under implication.
    pub authority: BTreeSet<String>,
    /// The granted effects as written.
    pub written: Vec<String>,
    /// The dependency's own manifest. A dependency with no `weft.toml` is a
    /// plain library.
    pub manifest: Option<Manifest>,
}

/// A loaded program: a file or a package directory.
#[derive(Clone, Debug)]
pub struct Package {
    /// The source of each unit: the prelude
    /// ([`PRELUDE_UNIT`](weft_syntax::diag::PRELUDE_UNIT)), the root
    /// ([`ROOT_UNIT`]), then the dependencies.
    pub files: Vec<SourceFile>,
    /// The parsed units.
    pub units: Vec<Unit>,
    /// The root manifest, for a package.
    pub manifest: Option<Manifest>,
    /// The dependencies.
    pub deps: Vec<Dependency>,
}

/// The profile that the flags choose. `None` keeps the value of the manifest
/// or of the file markers.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Profile {
    /// `--lib` (true) or `--bin` (false).
    pub library: Option<bool>,
    /// `--no-runtime` (true) or `--runtime` (false).
    pub no_runtime: Option<bool>,
}

impl Package {
    /// Returns the analysis options of the root. A package takes them from its
    /// manifest, a single file from its file markers (`// weft: library`). The
    /// flags win over both.
    pub fn options(&self, flags: Profile) -> weft_sema::Options {
        let own = match &self.manifest {
            Some(m) => weft_sema::Options {
                library: m.package.kind == Kind::Lib,
                no_runtime: m.package.runtime == Runtime::None,
                ..weft_sema::Options::default()
            },
            None => self
                .files
                .get(ROOT_UNIT)
                .map_or_else(weft_sema::Options::default, |f| {
                    weft_sema::Options::from_markers(&f.text)
                }),
        };
        weft_sema::Options {
            library: flags.library.unwrap_or(own.library),
            no_runtime: flags.no_runtime.unwrap_or(own.no_runtime),
            ..own
        }
    }

    /// W0804: a word in a file marker that is not a marker. A package takes
    /// its options from the manifest, so only a single file is checked.
    pub fn marker_diags(&self) -> Vec<Diagnostic> {
        let Some(f) = self
            .files
            .get(ROOT_UNIT)
            .filter(|_| self.manifest.is_none())
        else {
            return Vec::new();
        };
        weft_sema::marker_words(&f.text)
            .into_iter()
            .filter(|(_, w)| !weft_sema::MARKERS.contains(w))
            .map(|(at, w)| {
                let lo = u32::try_from(at).unwrap_or(u32::MAX);
                let hi = u32::try_from(at + w.len()).unwrap_or(u32::MAX);
                let mut d = Diagnostic::warning(
                    Code::W0804,
                    format!("unknown file marker `{w}`; it has no effect"),
                    weft_syntax::ast::Span::new(lo, hi),
                )
                .note(format!(
                    "the markers are `{}`",
                    weft_sema::MARKERS.join("`, `")
                ));
                d.unit = ROOT_UNIT;
                d
            })
            .collect()
    }
}

/// A source file that does not parse.
#[derive(Debug, thiserror::Error)]
#[error("{}", .diag.message)]
pub struct SyntaxError {
    /// The source file.
    pub file: SourceFile,
    /// W0001 at the location of the error.
    pub diag: Diagnostic,
}

fn parse_unit(name: &str, path: &Path) -> Result<(SourceFile, Unit)> {
    let text =
        fs::read_to_string(path).with_context(|| format!("cannot read {}", path.display()))?;
    let sf = SourceFile::new(path.display().to_string(), text);
    let file = parse_file(&sf.text).map_err(|e| SyntaxError {
        file: sf.clone(),
        diag: Diagnostic::error(Code::W0001, e.message, e.span),
    })?;
    Ok((
        sf,
        Unit {
            name: name.into(),
            file,
            is_std: false,
        },
    ))
}

/// Loads a file, or a package directory with `weft.toml`.
pub fn load(path: &Path) -> Result<Package> {
    if !path.exists() {
        bail!("cannot read {}: no such file or directory", path.display());
    }
    let prelude = weft_sema::prelude_unit()?;
    let mut files = vec![SourceFile::new("prelude.wf", weft_sema::PRELUDE_SRC)];
    let mut units = vec![prelude];
    if path.is_file() {
        let (sf, u) = parse_unit("", path)?;
        files.push(sf);
        units.push(u);
        return Ok(Package {
            files,
            units,
            manifest: None,
            deps: Vec::new(),
        });
    }
    let manifest = Manifest::read(&path.join("weft.toml"))?;
    let root_file = root_source(path, manifest.package.kind)?;
    let (sf, u) = parse_unit("", &root_file)?;
    files.push(sf);
    units.push(u);
    let mut deps = Vec::new();
    for (name, d) in &manifest.dependencies {
        let dir: PathBuf = path.join(&d.path);
        let dm_path = dir.join("weft.toml");
        let dm = if dm_path.exists() {
            Some(Manifest::read(&dm_path)?)
        } else {
            None
        };
        let src = root_source(&dir, Kind::Lib)?;
        let (sf, u) = parse_unit(name, &src)?;
        let mut authority = BTreeSet::new();
        for a in &d.authority {
            // Authority names standard effects: `net`, `log`, `io`, ...
            let canon = effects::std_alias(&a.to_ascii_lowercase())
                .with_context(|| format!("unknown effect `{a}` in the authority of `{name}`"))?;
            authority.extend(canon);
        }
        let authority = effects::close(&authority);
        deps.push(Dependency {
            name: name.clone(),
            unit: units.len(),
            authority,
            written: d.authority.clone(),
            manifest: dm,
        });
        files.push(sf);
        units.push(u);
    }
    Ok(Package {
        files,
        units,
        manifest: Some(manifest),
        deps,
    })
}

fn root_source(dir: &Path, kind: Kind) -> Result<PathBuf> {
    let main = dir.join("src/main.wf");
    let lib = dir.join("src/lib.wf");
    let pick = match kind {
        Kind::Bin if main.is_file() => main,
        _ if lib.is_file() => lib,
        _ if main.is_file() => main,
        _ => bail!("{} has no src/main.wf or src/lib.wf", dir.display()),
    };
    Ok(pick)
}

/// W0901 and W0902: dependency authority and the GC switch.
pub fn package_diags(pkg: &Package, a: &Analysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    if let Some(m) = &pkg.manifest {
        if m.package.gc && m.package.kind == Kind::Lib {
            let mut d = Diagnostic::error(
                Code::W0902,
                "a library cannot enable the GC tier; only a binary may",
                weft_syntax::ast::Span::default(),
            )
            .note("weft.toml sets `gc = true` in [package]");
            d.unit = ROOT_UNIT;
            out.push(d);
        }
    }
    for dep in &pkg.deps {
        if dep.manifest.as_ref().is_some_and(|m| m.package.gc) {
            let mut d = Diagnostic::error(
                Code::W0902,
                format!(
                    "dependency `{}` enables the GC tier; libraries may never require it",
                    dep.name
                ),
                weft_syntax::ast::Span::default(),
            );
            d.unit = dep.unit;
            out.push(d);
        }
        for (i, f) in a.program.fn_ids().zip(&a.program.fns) {
            // Each function of the dependency counts, also a private one: a public
            // function or a returned closure can run it. A function needs what it
            // states and what its body does, with the closures that the body makes
            // and returns, also a closure that the body does not call.
            if a.program.mods[f.module].unit != dep.unit {
                continue;
            }
            // Authority names standard effects only. A user effect of the
            // dependency needs a handler of the caller, not authority. The facts
            // name a user effect by its identity (`dep.Log`), so a user effect with
            // the name of a standard effect does not count either.
            let mut performs = a.sigs[i].effects.named.clone();
            for b in a.bodies.iter().filter(|b| b.func == Some(i)) {
                performs.extend(b.effects.named.iter().cloned());
                performs.extend(b.facts.escapes_at.iter().map(|(_, e)| e.clone()));
            }
            performs.retain(|e| effects::is_std(e));
            let needs: BTreeSet<String> = effects::close(&performs);
            let extra: Vec<&String> = needs
                .iter()
                .filter(|e| !dep.authority.contains(*e))
                .collect();
            if extra.is_empty() {
                continue;
            }
            let wanted: Vec<String> = extra.iter().map(|e| effects::in_signature(e)).collect();
            let mut d = Diagnostic::error(
                Code::W0901,
                format!(
                    "dependency `{}` function `{}` needs `{}`, but the project grants `{}` only [{}]",
                    dep.name,
                    f.path,
                    wanted.join(", "),
                    dep.name,
                    dep.written.join(", ")
                ),
                f.decl.name.span,
            )
            .note(format!("grant it in weft.toml: [dependencies.{}] authority = [\"{}\"]", dep.name, wanted.join("\", \"")));
            d.unit = dep.unit;
            out.push(d);
        }
    }
    out
}
