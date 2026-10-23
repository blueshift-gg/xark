//! Spill storage for the low-memory quotient step: one domain-sized vector parked
//! outside the working set (a temp file natively, a JS buffer in WASM) while the
//! next one is computed, then read back block by block.

use std::fs::File;
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

use ark_bn254::Fr;

use crate::accel::fr_bytes_mut;

/// A parked field vector.
pub trait Spill {
    /// Store `data`, replacing anything stored before.
    fn store(&mut self, data: &[Fr]) -> std::io::Result<()>;
    /// Read elements `[off, off + out.len())` of the stored vector.
    fn load(&mut self, off: usize, out: &mut [Fr]) -> std::io::Result<()>;
}

/// Raw bytes of a field slice (Montgomery limbs; read back by the same build).
pub(crate) fn fr_bytes(v: &[Fr]) -> &[u8] {
    // SAFETY: `Fr` is four `u64` limbs with no padding.
    unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, std::mem::size_of_val(v)) }
}

/// A temp file, deleted on drop.
pub struct FileSpill {
    file: File,
    path: PathBuf,
}

impl FileSpill {
    /// Create a fresh spill file in `dir`.
    pub fn new_in(dir: &Path) -> std::io::Result<Self> {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let path = dir.join(format!(".xark-spill-{}-{nanos}.bin", std::process::id()));
        let file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .open(&path)?;
        Ok(FileSpill { file, path })
    }
}

impl Drop for FileSpill {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
    }
}

impl Spill for FileSpill {
    fn store(&mut self, data: &[Fr]) -> std::io::Result<()> {
        self.file.seek(SeekFrom::Start(0))?;
        self.file.write_all(fr_bytes(data))?;
        self.file.flush()
    }
    fn load(&mut self, off: usize, out: &mut [Fr]) -> std::io::Result<()> {
        self.file.seek(SeekFrom::Start(off as u64 * 32))?;
        self.file.read_exact(fr_bytes_mut(out))
    }
}

/// In memory (for tests: exercises the spill path without I/O).
#[derive(Default)]
pub struct MemSpill(Vec<Fr>);

impl Spill for MemSpill {
    fn store(&mut self, data: &[Fr]) -> std::io::Result<()> {
        self.0.clear();
        self.0.extend_from_slice(data);
        Ok(())
    }
    fn load(&mut self, off: usize, out: &mut [Fr]) -> std::io::Result<()> {
        out.copy_from_slice(&self.0[off..off + out.len()]);
        Ok(())
    }
}
