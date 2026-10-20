//! The archive of the tier-2 probes (plan §2.1).
//!
//! The archive is a tar file, compressed with zstd. It holds each path of the
//! manifest (also the other paths of an entry, so that a manifest of the unpacked
//! archive is equal to the manifest of the source), the files of each package, and
//! the manifest text as `manifest.tsv`. The archive is reproducible: the names are in
//! sorted order, and each header has the time 0, the owner 0 and the mode `0644`.

use std::fs::{self, File};
use std::io::{self, BufReader, BufWriter, Read, Write};
use std::path::Path;

use sha2::{Digest, Sha256};

use crate::manifest::{package_files, Manifest, Mode};
use crate::Error;

/// The name of the manifest text in the archive.
pub const MANIFEST_NAME: &str = "manifest.tsv";

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
