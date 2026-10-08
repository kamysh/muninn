//! Describe the complete removal target before indexing coordination begins.
use std::io::{self, BufRead, Write};
use std::path::Path;

pub struct Target<'a> {
    pub path: &'a Path,
    pub registered_name: Option<&'a str>,
}

fn visible(text: &str) -> String {
    text.chars()
        .flat_map(|c| {
            if c.is_control() {
                c.escape_default().collect::<Vec<_>>()
            } else {
                vec![c]
            }
        })
        .collect()
}

/// Returns false for absent targets, negative answers, empty answers, and EOF.
/// The caller must return before acquiring indexing locks when this is false.
pub fn confirm(
    target: &Target<'_>,
    yes: bool,
    input: &mut impl BufRead,
    output: &mut impl Write,
) -> io::Result<bool> {
    let path = visible(&target.path.to_string_lossy());
    if let Some(name) = target.registered_name {
        writeln!(output, "Repository: {}", visible(name))?;
        writeln!(output, "Registered path: {path}")?;
        writeln!(
            output,
            "Removal will unregister this repository and delete all its index data,"
        )?;
        writeln!(output, "including every indexed worktree.")?;
    } else {
        writeln!(
            output,
            "No registered repository at {path}. Nothing to remove."
        )?;
        return Ok(false);
    }
    if yes {
        return Ok(true);
    }
    write!(output, "Confirm removal? [y/N] ")?;
    output.flush()?;
    let mut answer = String::new();
    input.read_line(&mut answer)?;
    let confirmed = answer.trim().eq_ignore_ascii_case("y");
    if !confirmed {
        writeln!(output, "Aborted. Nothing removed.")?;
    }
    Ok(confirmed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn registered_repository_has_explicit_removal_scope() {
        let target = Target {
            path: Path::new("/repo"),
            registered_name: Some("Example"),
        };
        let mut output = Vec::new();
        assert!(!confirm(&target, false, &mut Cursor::new(b"n\n"), &mut output).unwrap());
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("Repository: Example"));
        assert!(output.contains("Registered path: /repo"));
        assert!(output.contains("including every indexed worktree"));
        assert!(output.contains("Confirm removal? [y/N]"));
        assert!(!output.contains("anyway"));
    }

    #[test]
    fn negative_empty_and_eof_answers_cancel_removal() {
        let target = Target {
            path: Path::new("/repo"),
            registered_name: Some("Example"),
        };
        for answer in ["n\n", "\n", "", "yes\n"] {
            let mut output = Vec::new();
            assert!(!confirm(&target, false, &mut Cursor::new(answer), &mut output).unwrap());
            assert!(String::from_utf8(output)
                .unwrap()
                .contains("Aborted. Nothing removed."));
        }
    }

    #[test]
    fn absent_target_does_not_prompt_or_consume_confirmation() {
        let target = Target {
            path: Path::new("/missing"),
            registered_name: None,
        };
        let mut input = Cursor::new("y\n");
        let mut output = Vec::new();
        assert!(!confirm(&target, true, &mut input, &mut output).unwrap());
        assert_eq!(input.position(), 0);
        assert_eq!(
            String::from_utf8(output).unwrap(),
            "No registered repository at /missing. Nothing to remove.\n"
        );
    }

    #[test]
    fn explicit_confirmation_and_yes_flag_preserve_existing_controls() {
        let target = Target {
            path: Path::new("/repo"),
            registered_name: Some("Example"),
        };
        for answer in ["y\n", "Y\n"] {
            assert!(confirm(&target, false, &mut Cursor::new(answer), &mut Vec::new()).unwrap());
        }
        let mut input = Cursor::new("n\n");
        let mut output = Vec::new();
        assert!(confirm(&target, true, &mut input, &mut output).unwrap());
        assert_eq!(input.position(), 0);
        assert!(!String::from_utf8(output).unwrap().contains("[y/N]"));
    }

    #[test]
    fn names_cannot_inject_terminal_controls_or_extra_scope_lines() {
        let target = Target {
            path: Path::new("/repo"),
            registered_name: Some("Example\n\x1b[31m"),
        };
        let mut output = Vec::new();
        confirm(&target, false, &mut Cursor::new("n\n"), &mut output).unwrap();
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("Example\\n\\u{1b}[31m"));
        assert!(!output.contains('\x1b'));
    }
}
