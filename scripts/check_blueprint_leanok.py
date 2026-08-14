#!/usr/bin/env python3
"""Check that blueprint declarations marked \leanok do not depend on sorryAx.

Only declarations listed by \lean{...} inside a theorem-like environment that
also contains \leanok are checked. Declarations without \leanok are ignored.
"""

from __future__ import annotations

from pathlib import Path
import re
import subprocess
import sys
import tempfile

BLUEPRINT_DIR = Path("blueprint/src/theorems")
THEOREM_ENVS = "definition|lemma|proposition|theorem|corollary"
ENV_RE = re.compile(
    rf"\\begin\{{(?P<env>{THEOREM_ENVS})\}}(?P<body>.*?)"
    rf"\\end\{{(?P=env)\}}",
    re.DOTALL,
)
LEAN_RE = re.compile(r"\\lean\{([^}]*)\}")
LEANOK_RE = re.compile(r"\\leanok\b")


def collect_leanok_declarations() -> dict[str, set[Path]]:
    declarations: dict[str, set[Path]] = {}

    for tex_file in sorted(BLUEPRINT_DIR.glob("*.tex")):
        text = tex_file.read_text(encoding="utf-8")
        for match in ENV_RE.finditer(text):
            body = match.group("body")
            if not LEANOK_RE.search(body):
                continue

            for lean_match in LEAN_RE.finditer(body):
                for raw_decl in lean_match.group(1).split(","):
                    decl = raw_decl.strip()
                    if decl:
                        declarations.setdefault(decl, set()).add(tex_file)

    return declarations


def main() -> int:
    declarations = collect_leanok_declarations()

    if not declarations:
        print("No \\leanok declarations found; nothing to check.")
        return 0

    # Print each declaration's transitive axiom dependencies in a single Lean
    # invocation. `#print axioms` reports sorryAx if the declaration itself or
    # any theorem it depends on contains `sorry`.
    source = ["import FormalQualBench", ""]
    for decl in sorted(declarations):
        source.append(f"#print axioms {decl}")

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", encoding="utf-8", delete=False
    ) as tmp:
        tmp.write("\n".join(source) + "\n")
        tmp_path = Path(tmp.name)

    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(tmp_path)],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
    finally:
        tmp_path.unlink(missing_ok=True)

    output = proc.stdout
    if proc.returncode != 0:
        print("Lean failed while checking \\leanok declarations:\n")
        print(output)
        return proc.returncode

    failures: list[str] = []

    for decl in sorted(declarations):
        # Lean prints either
        #   'Foo.bar' depends on axioms: [ ... ]
        # or
        #   'Foo.bar' does not depend on any axioms
        # The axiom list may span multiple lines.
        pattern = re.compile(
            rf"'{re.escape(decl)}' depends on axioms:\s*\[(.*?)\]",
            re.DOTALL,
        )
        match = pattern.search(output)
        if match and re.search(r"\bsorryAx\b", match.group(1)):
            failures.append(decl)
            files = ", ".join(str(p) for p in sorted(declarations[decl]))
            print(f"✗ {decl} depends on sorryAx  ({files})")
        else:
            print(f"✓ {decl}")

    if failures:
        print("\nERROR: declarations marked \\leanok must not depend on sorryAx.")
        print(f"Found {len(failures)} failing declaration(s).")
        return 1

    print(
        f"\nChecked {len(declarations)} declaration(s) marked \\leanok: "
        "no sorryAx dependencies found."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
