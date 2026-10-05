use anyhow::{bail, ensure, Result};
use std::path::{Path, PathBuf};

/// Lossless canonical locator. Database reads decode without requiring a path to
/// still exist; new locators must be canonicalized against the filesystem.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StoredPath {
    encoding: String,
    bytes: Vec<u8>,
}

impl StoredPath {
    pub async fn canonicalize(path: &Path) -> Result<Self> {
        Self::encode(&tokio::fs::canonicalize(path).await?)
    }

    fn encode(path: &Path) -> Result<Self> {
        ensure!(path.is_absolute(), "identity path must be absolute");
        #[cfg(unix)]
        let (encoding, bytes) = {
            use std::os::unix::ffi::OsStrExt;
            ("unix-bytes", path.as_os_str().as_bytes().to_vec())
        };
        #[cfg(windows)]
        let (encoding, bytes) = {
            use std::os::windows::ffi::OsStrExt;
            (
                "windows-utf16le",
                path.as_os_str()
                    .encode_wide()
                    .flat_map(u16::to_le_bytes)
                    .collect(),
            )
        };
        Self::from_db(encoding, bytes)
    }

    pub fn encoding(&self) -> &str {
        &self.encoding
    }
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub(crate) fn from_db(encoding: &str, bytes: Vec<u8>) -> Result<Self> {
        ensure!(!bytes.is_empty(), "empty identity path");
        match encoding {
            "unix-bytes" => ensure!(!bytes.contains(&0), "NUL in Unix identity path"),
            "windows-utf16le" => {
                ensure!(bytes.len() % 2 == 0, "odd UTF-16 path length");
                ensure!(
                    !bytes.chunks_exact(2).any(|b| b == [0, 0]),
                    "NUL in Windows identity path"
                );
            }
            _ => bail!("unsupported path encoding: {encoding}"),
        }
        let value = Self {
            encoding: encoding.to_owned(),
            bytes,
        };
        // Foreign-platform rows can be inspected as bytes but cannot be used as
        // local paths. Their encoding remains part of family identity.
        #[cfg(unix)]
        let native = encoding == "unix-bytes";
        #[cfg(windows)]
        let native = encoding == "windows-utf16le";
        if native {
            let path = value.to_path_buf()?;
            ensure!(path.is_absolute(), "stored identity path is not absolute");
            ensure!(
                !path
                    .components()
                    .any(|c| matches!(c, std::path::Component::ParentDir)),
                "parent component in identity path"
            );
        }
        Ok(value)
    }

    pub fn to_path_buf(&self) -> Result<PathBuf> {
        #[cfg(unix)]
        {
            use std::os::unix::ffi::OsStringExt;
            ensure!(
                self.encoding == "unix-bytes",
                "identity belongs to another path platform"
            );
            Ok(std::ffi::OsString::from_vec(self.bytes.clone()).into())
        }
        #[cfg(windows)]
        {
            use std::os::windows::ffi::OsStringExt;
            ensure!(
                self.encoding == "windows-utf16le",
                "identity belongs to another path platform"
            );
            let units: Vec<_> = self
                .bytes
                .chunks_exact(2)
                .map(|b| u16::from_le_bytes([b[0], b[1]]))
                .collect();
            Ok(std::ffi::OsString::from_wide(&units).into())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn path_survives_removal_and_never_recanonicalizes_on_decode() {
        let temp = tempfile::tempdir().unwrap();
        let directory = temp.path().join("identity with spaces");
        std::fs::create_dir(&directory).unwrap();
        let stored = StoredPath::canonicalize(&directory).await.unwrap();
        let canonical = directory.canonicalize().unwrap();
        std::fs::remove_dir(&directory).unwrap();
        let decoded = StoredPath::from_db(stored.encoding(), stored.bytes().to_vec()).unwrap();
        assert_eq!(decoded.to_path_buf().unwrap(), canonical);
        assert!(StoredPath::canonicalize(&directory).await.is_err());
        assert!(StoredPath::encode(Path::new("relative")).is_err());
    }

    #[cfg(unix)]
    #[tokio::test]
    async fn native_bytes_and_symlink_aliases_are_lossless() {
        use std::os::unix::ffi::OsStringExt;
        let temp = tempfile::tempdir().unwrap();
        let path = temp
            .path()
            .join(std::ffi::OsString::from_vec(b"repo \xff\n".to_vec()));
        std::fs::create_dir(&path).unwrap();
        let alias = temp.path().join("alias");
        std::os::unix::fs::symlink(&path, &alias).unwrap();
        let key = StoredPath::canonicalize(&path).await.unwrap();
        assert_eq!(key, StoredPath::canonicalize(&alias).await.unwrap());
        assert_eq!(key.to_path_buf().unwrap(), path.canonicalize().unwrap());
        assert!(key.bytes().ends_with(b"\xff\n"));
    }

    #[test]
    fn malformed_encodings_are_rejected() {
        for (encoding, bytes) in [
            ("utf8", b"/path".to_vec()),
            ("unix-bytes", vec![]),
            ("unix-bytes", b"/bad\0path".to_vec()),
            ("windows-utf16le", vec![65]),
            ("windows-utf16le", vec![0, 0]),
        ] {
            assert!(StoredPath::from_db(encoding, bytes).is_err());
        }
    }

    #[cfg(windows)]
    #[test]
    fn windows_unpaired_surrogates_roundtrip() {
        use std::os::windows::ffi::OsStringExt;
        let path = PathBuf::from(std::ffi::OsString::from_wide(&[67, 58, 92, 0xd800]));
        assert_eq!(
            StoredPath::encode(&path).unwrap().to_path_buf().unwrap(),
            path
        );
    }
}
