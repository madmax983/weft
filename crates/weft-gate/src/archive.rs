//! The archive of the tier-2 probes (plan §2.1).
//!
//! The archive is a tar file, compressed with zstd. It holds each path of the
//! manifest (also the other paths of an entry, so that a manifest of the unpacked
//! archive is equal to the manifest of the source), the files of each package, and
//! the manifest text as `manifest.tsv`. The archive is reproducible: the names are in
//! sorted order, and each header has the time 0, the owner 0 and the mode `0644`.
//!
//! The repository holds the archive ([`COMMITTED_ARCHIVE`]) and its hash
//! ([`COMMITTED_HASH`]). The default root of tier 2 is this archive, unpacked into
//! [`UNPACKED_DIR`] when it is necessary ([`default_probes`]).

use std::ffi::OsString;
use std::fs::{self, File};
use std::io::{self, BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use crate::manifest::{package_files, Manifest, Mode};
use crate::Error;

/// The name of the manifest text in the archive.
pub const MANIFEST_NAME: &str = "manifest.tsv";

/// The committed archive of the tier-2 probes, relative to the repository.
pub const COMMITTED_ARCHIVE: &str = "tests/gate/probes-tier2.tar.zst";

/// The committed SHA-256 of [`COMMITTED_ARCHIVE`], relative to the repository. The
/// first word of the file is the hash in lower-case hex.
pub const COMMITTED_HASH: &str = "tests/gate/probes-tier2.sha256";

/// The directory of the unpacked committed archive, relative to the repository.
pub const UNPACKED_DIR: &str = "target/gate/probes-tier2";

/// The file in [`UNPACKED_DIR`] that records the hash of the unpacked archive.
const STAMP: &str = ".sha256";

/// The zstd level.
const LEVEL: i32 = 19;

/// The zstd window: 2^27 bytes (128 MiB). A decoder accepts this window without a
/// special option, and the long matches find the copies of a probe.
const WINDOW_LOG: u32 = 27;

/// Where the bytes of a file of the archive come from.
enum Source {
    Disk(std::path::PathBuf),
    Text(Vec<u8>),
}

/// Writes the archive of `manifest` (with its files below `base`) to `out`. Returns
/// the SHA-256 of the archive in lower-case hex.
pub fn write(base: &Path, manifest: &Manifest, out: &Path) -> Result<String, Error> {
    let mut files: Vec<(String, Source)> = vec![(
        MANIFEST_NAME.to_string(),
        Source::Text(manifest.to_tsv().into_bytes()),
    )];
    for (entry, path) in manifest.all_paths() {
        match entry.mode {
            Mode::File => files.push((path.to_string(), Source::Disk(base.join(path)))),
            Mode::Package => {
                let dir = base.join(path);
                for rel in package_files(&dir)? {
                    let full = dir.join(&rel);
                    files.push((format!("{path}/{rel}"), Source::Disk(full)));
                }
            }
        }
    }
    files.sort_by(|a, b| a.0.cmp(&b.0));
    files.dedup_by(|a, b| a.0 == b.0);

    if let Some(dir) = out.parent() {
        fs::create_dir_all(dir).map_err(|e| Error::io(dir, e))?;
    }
    let io_err = |e: io::Error| Error::io(out, e);
    let file = File::create(out).map_err(io_err)?;
    let mut enc = zstd::Encoder::new(BufWriter::new(file), LEVEL).map_err(io_err)?;
    enc.long_distance_matching(true).map_err(io_err)?;
    enc.window_log(WINDOW_LOG).map_err(io_err)?;
    enc.include_checksum(true).map_err(io_err)?;
    let mut tar = tar::Builder::new(enc);
    for (name, source) in &files {
        let bytes = match source {
            Source::Disk(p) => fs::read(p).map_err(|e| Error::io(p, e))?,
            Source::Text(t) => t.clone(),
        };
        let mut header = tar::Header::new_gnu();
        header.set_entry_type(tar::EntryType::Regular);
        header.set_size(bytes.len() as u64);
        header.set_mode(0o644);
        header.set_mtime(0);
        header.set_uid(0);
        header.set_gid(0);
        tar.append_data(&mut header, name, bytes.as_slice())
            .map_err(io_err)?;
    }
    let enc = tar.into_inner().map_err(io_err)?;
    let mut buf = enc.finish().map_err(io_err)?;
    buf.flush().map_err(io_err)?;
    drop(buf);
    sha256_file(out)
}

/// Lists the names in the archive `path`, in archive order.
pub fn list(path: &Path) -> Result<Vec<String>, Error> {
    let io_err = |e: io::Error| Error::io(path, e);
    let file = File::open(path).map_err(io_err)?;
    let mut dec = zstd::Decoder::new(file).map_err(io_err)?;
    dec.window_log_max(WINDOW_LOG).map_err(io_err)?;
    let mut ar = tar::Archive::new(dec);
    let mut out = Vec::new();
    for ent in ar.entries().map_err(io_err)? {
        let ent = ent.map_err(io_err)?;
        let p = ent.path().map_err(io_err)?;
        out.push(p.to_string_lossy().into_owned());
    }
    Ok(out)
}

/// Unpacks the archive `path` into the directory `dest`. Then `WEFT_GATE_PROBES` can
/// name `dest`.
pub fn unpack(path: &Path, dest: &Path) -> Result<(), Error> {
    let io_err = |e: io::Error| Error::io(path, e);
    fs::create_dir_all(dest).map_err(|e| Error::io(dest, e))?;
    let file = File::open(path).map_err(io_err)?;
    let mut dec = zstd::Decoder::new(file).map_err(io_err)?;
    dec.window_log_max(WINDOW_LOG).map_err(io_err)?;
    tar::Archive::new(dec).unpack(dest).map_err(io_err)
}

/// The SHA-256 of the file `path`, in lower-case hex.
pub fn sha256_file(path: &Path) -> Result<String, Error> {
    let io_err = |e: io::Error| Error::io(path, e);
    let mut r = BufReader::new(File::open(path).map_err(io_err)?);
    let mut h = Sha256::new();
    let mut buf = vec![0u8; 1 << 16];
    loop {
        let n = r.read(&mut buf).map_err(io_err)?;
        if n == 0 {
            break;
        }
        h.update(buf.get(..n).unwrap_or_default());
    }
    Ok(crate::manifest::hex(&h.finalize()))
}

/// Reads the committed hash of the archive (the first word of [`COMMITTED_HASH`]).
pub fn committed_hash(repo: &Path) -> Result<String, Error> {
    let path = repo.join(COMMITTED_HASH);
    let text = fs::read_to_string(&path).map_err(|e| Error::io(&path, e))?;
    Ok(text
        .split_whitespace()
        .next()
        .unwrap_or_default()
        .to_string())
}

/// Makes sure that the SHA-256 of the file `path` is `expected`.
pub fn check_hash(path: &Path, expected: &str) -> Result<(), Error> {
    let found = sha256_file(path)?;
    if found == expected {
        Ok(())
    } else {
        Err(Error::Hash {
            path: path.to_path_buf(),
            expected: expected.to_string(),
            found,
        })
    }
}

/// The default root of tier 2: the committed archive of `repo`, unpacked into
/// [`UNPACKED_DIR`].
///
/// If the directory records the committed hash, this function does not unpack
/// again. Else it checks the hash of the archive, unpacks it into a new directory,
/// records the hash, and then puts the directory in the place of the old one.
pub fn default_probes(repo: &Path) -> Result<PathBuf, Error> {
    let expected = committed_hash(repo)?;
    let dest = repo.join(UNPACKED_DIR);
    let stamp = dest.join(STAMP);
    if fs::read_to_string(&stamp).is_ok_and(|s| s.trim() == expected) {
        return Ok(dest);
    }
    let file = repo.join(COMMITTED_ARCHIVE);
    check_hash(&file, &expected)?;
    let mut partial = dest.clone().into_os_string();
    partial.push(".partial");
    let partial = PathBuf::from(partial);
    remove_dir(&partial)?;
    unpack(&file, &partial)?;
    let new_stamp = partial.join(STAMP);
    fs::write(&new_stamp, format!("{expected}\n")).map_err(|e| Error::io(&new_stamp, e))?;
    remove_dir(&dest)?;
    fs::rename(&partial, &dest).map_err(|e| Error::io(&dest, e))?;
    Ok(dest)
}

/// The root of tier 2: the value of the flag `--probes`, else the value of the
/// environment variable `WEFT_GATE_PROBES`, else [`default_probes`].
pub fn probes_root(
    repo: &Path,
    flag: Option<PathBuf>,
    env: Option<OsString>,
) -> Result<PathBuf, Error> {
    match flag.or_else(|| env.map(PathBuf::from)) {
        Some(p) => Ok(p),
        None => default_probes(repo),
    }
}

/// Removes the directory `dir` and its contents, if it exists.
fn remove_dir(dir: &Path) -> Result<(), Error> {
    match fs::remove_dir_all(dir) {
        Err(e) if e.kind() != io::ErrorKind::NotFound => Err(Error::io(dir, e)),
        _ => Ok(()),
    }
}
