#!/usr/bin/env python3
"""Strip the `private` modifier from every Main.lean under FormalQualBench/.

Turns declarations like

    private theorem foo ...
    @[simp] private lemma bar ...

into their public counterparts. Only the standalone word `private` followed by
whitespace is removed, so identifiers such as `privateKey` are left alone.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# `private` as a whole word, plus the whitespace that separates it from the
# declaration keyword. Anchored on a word boundary so `myprivate`/`privateFoo`
# are untouched.
PRIVATE_RE = re.compile(r"\bprivate[ \t]+")


def strip_private(text: str) -> tuple[str, int]:
    new_text, count = PRIVATE_RE.subn("", text)
    return new_text, count


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "root",
        nargs="?",
        default=Path(__file__).resolve().parent / "FormalQualBench",
        type=Path,
        help="folder holding the per-problem directories (default: ./FormalQualBench)",
    )
    parser.add_argument(
        "-n",
        "--dry-run",
        action="store_true",
        help="report what would change without writing files",
    )
    args = parser.parse_args()

    root: Path = args.root
    if not root.is_dir():
        print(f"error: {root} is not a directory", file=sys.stderr)
        return 1

    files = sorted(p for p in root.glob("*/Main.lean") if ".lake" not in p.parts)
    if not files:
        print(f"no Main.lean files found under {root}", file=sys.stderr)
        return 1

    total = 0
    changed = 0
    for path in files:
        original = path.read_text(encoding="utf-8")
        updated, count = strip_private(original)
        if count == 0:
            continue
        total += count
        changed += 1
        if not args.dry_run:
            path.write_text(updated, encoding="utf-8")
        print(f"{path.relative_to(root.parent)}: {count} removed")

    verb = "would remove" if args.dry_run else "removed"
    print(f"\n{verb} {total} `private` modifier(s) across {changed} file(s) "
          f"({len(files)} scanned)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
