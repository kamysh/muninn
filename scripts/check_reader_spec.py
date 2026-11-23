#!/usr/bin/env python3
"""Type-check the Agda aggregate and verify its reader topics and links."""

import argparse
from contextlib import ExitStack
from pathlib import Path
import re
import subprocess
import tempfile
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]
SPEC = ROOT / "spec"
GUIDE = ROOT / "SPEC-READING-GUIDE.md"
LINK = re.compile(r"\[[^\]\n]+\]\(([^()\s]+)\)")


def check_links(document):
    targets = set()
    inside_fence = False
    for number, line in enumerate(document.read_text().splitlines(), 1):
        if line.lstrip().startswith("```"):
            inside_fence = not inside_fence
            continue
        if inside_fence:
            continue
        for destination in LINK.findall(line):
            url = urlsplit(destination)
            if url.scheme or url.netloc or not url.path:
                continue
            target = (document.parent / unquote(url.path)).resolve()
            if not target.is_relative_to(ROOT) or not target.exists():
                raise ValueError(f"{document.relative_to(ROOT)}:{number}: invalid link {destination}")
            targets.add(target)
    return targets


def check_topics(output):
    if GUIDE not in check_links(ROOT / "README.md"):
        raise ValueError("README does not link to the reader guide")
    topics = sorted((SPEC / "Muninn").rglob("*.lagda.md"))
    if not topics:
        raise ValueError("no literate Agda reader topics found")
    listed = check_links(GUIDE)
    for topic in topics:
        if topic not in listed:
            raise ValueError(f"{topic.relative_to(ROOT)} is missing from the reader guide")
        check_links(topic)

    subprocess.run(
        ["agda", "--html", "--html-highlight=auto", "--html-dir", str(output), "Muninn.agda"],
        cwd=SPEC,
        check=True,
    )
    for topic in topics:
        module = ".".join(topic.relative_to(SPEC).parts).removesuffix(".lagda.md")
        page = output / f"{module}.md"
        rendered = page.read_text() if page.is_file() else ""
        if not re.search(r"^# \S", rendered, re.MULTILINE) or '<pre class="Agda">' not in rendered:
            raise ValueError(f"{topic.relative_to(ROOT)} did not render prose and checked Agda")
    print(f"Checked and rendered {len(topics)} reader topics.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="new directory for the rendered pages")
    args = parser.parse_args()
    with ExitStack() as stack:
        if args.output is None:
            output = Path(stack.enter_context(tempfile.TemporaryDirectory()))
        else:
            output = args.output.resolve()
            output.mkdir()
        check_topics(output)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        raise SystemExit(f"Reader specification check: {error}") from error
