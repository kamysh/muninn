use std::collections::BTreeSet;
use std::fs;
use std::io;
use std::path::{Component, Path, PathBuf};

pub(crate) fn has_alias(root: &Path, relative: &Path, include_leaf: bool) -> bool {
    let mut path = root.to_owned();
    let mut components = relative.components().peekable();
    while let Some(component) = components.next() {
        if !include_leaf && components.peek().is_none() {
            break;
        }
        path.push(component);
        if fs::symlink_metadata(&path).is_ok_and(|meta| meta.is_symlink()) {
            return true;
        }
    }
    false
}

pub(crate) fn visit_files(
    root: &Path,
    relative: &Path,
    selected: impl Fn(&Path, bool) -> bool,
    mut file: impl FnMut(&Path, PathBuf),
    mut unreadable: impl FnMut(&Path, io::Error),
) {
    let mut ancestors = relative
        .ancestors()
        .skip(1)
        .map(|parent| root.join(parent))
        .collect();
    visit(
        root,
        relative,
        &mut ancestors,
        &selected,
        &mut file,
        &mut unreadable,
    );
}

fn visit(
    root: &Path,
    relative: &Path,
    ancestors: &mut BTreeSet<PathBuf>,
    selected: &impl Fn(&Path, bool) -> bool,
    file: &mut impl FnMut(&Path, PathBuf),
    unreadable: &mut impl FnMut(&Path, io::Error),
) {
    let result = (|| {
        let Some(physical) = internal_path(root, relative)? else {
            return Ok(());
        };
        let metadata = fs::metadata(&physical)?;
        if metadata.is_file() {
            if selected(relative, false) {
                file(relative, physical);
            }
        } else if metadata.is_dir()
            && selected(relative, true)
            && ancestors.insert(physical.clone())
        {
            let children = fs::read_dir(&physical);
            match children {
                Ok(children) => {
                    for child in children {
                        match child {
                            Ok(child) => visit(
                                root,
                                &relative.join(child.file_name()),
                                ancestors,
                                selected,
                                file,
                                unreadable,
                            ),
                            Err(error) => unreadable(relative, error),
                        }
                    }
                }
                Err(error) => unreadable(relative, error),
            }
            ancestors.remove(&physical);
        }
        Ok::<_, io::Error>(())
    })();
    if let Err(error) = result {
        unreadable(relative, error);
    }
}

/// Resolve every expansion inside the checkout. Administrative files never
/// become source through an alias. The returned path contains no symlinks.
pub(crate) fn internal_path(root: &Path, relative: &Path) -> io::Result<Option<PathBuf>> {
    let mut resolved = root.to_owned();
    if resolve(root, relative, &mut resolved, &mut BTreeSet::new())? {
        Ok(Some(resolved))
    } else {
        Ok(None)
    }
}

fn resolve(
    root: &Path,
    path: &Path,
    resolved: &mut PathBuf,
    active: &mut BTreeSet<PathBuf>,
) -> io::Result<bool> {
    for component in path.components() {
        match component {
            Component::CurDir => continue,
            Component::ParentDir if resolved != root => {
                if !fs::metadata(&*resolved)?.is_dir() {
                    return Ok(false);
                }
                resolved.pop();
            }
            Component::Normal(name) if name != ".git" => {
                let next = resolved.join(name);
                let metadata = match fs::symlink_metadata(&next) {
                    Ok(metadata) => metadata,
                    Err(error)
                        if matches!(
                            error.kind(),
                            io::ErrorKind::NotFound | io::ErrorKind::NotADirectory
                        ) =>
                    {
                        return Ok(false)
                    }
                    Err(error) => return Err(error),
                };
                if metadata.is_symlink() {
                    if !active.insert(next.clone()) {
                        return Ok(false);
                    }
                    let target = fs::read_link(&next)?;
                    let target = if target.is_absolute() {
                        let Ok(inside) = target.strip_prefix(root) else {
                            return Ok(false);
                        };
                        *resolved = root.to_owned();
                        inside
                    } else {
                        &target
                    };
                    if !resolve(root, target, resolved, active)? {
                        return Ok(false);
                    }
                    active.remove(&next);
                } else {
                    *resolved = next;
                }
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}
