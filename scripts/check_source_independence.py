#!/usr/bin/env python3
"""Reject every source-level dependency on the retired stability-code source.

This is intentionally a repository-wide zero-import gate.  It has no
allowlist: the retired module root and the two former bridge roots may not be
imported by any tracked Lean source.  It also rejects restoration of the
deleted source/bridge paths or the two exact copied helper files that were
replaced by owner-native proofs.

"Repository-wide" means *this* checkout.  The walk stops at any nested
checkout, because those files are another working tree's, not this one's.
"""

from __future__ import annotations

import os
import pathlib
import re
import sys
from typing import Iterator


ROOT = pathlib.Path(__file__).resolve().parent.parent
IMPORT = re.compile(r"^\s*import\s+(\S+)")
SKIP_DIRS = (".lake", ".git")
FORBIDDEN_MODULE_ROOTS = (
    "BridgelandStability",
    "BridgelandStabLean",
    "CohLean",
    "DGLean",
)
FORBIDDEN_PATHS = (
    ROOT / "vendor" / "BridgelandStability",
    ROOT / "BridgelandStabLean",
    ROOT / "BridgelandStabLean.lean",
    ROOT / "CohLean",
    ROOT / "CohLean.lean",
    ROOT / "DGLean",
    ROOT / "DGLean.lean",
    ROOT
    / "DerivedAlgGeo"
    / "CategoryTheory"
    / "ObjectProperty"
    / "FullSubcategory.lean",
    ROOT
    / "DerivedAlgGeo"
    / "CategoryTheory"
    / "Triangulated"
    / "TStructure"
    / "HeartAbelian.lean",
)


def is_forbidden_module(module: str) -> bool:
    return any(
        module == root or module.startswith(root + ".")
        for root in FORBIDDEN_MODULE_ROOTS
    )


def lean_sources(root: pathlib.Path) -> Iterator[pathlib.Path]:
    """Yield this checkout's Lean sources, skipping build output and nested checkouts.

    Both the agent loop and `git worktree add` park working trees under
    `.claude/worktrees/`, and a worktree of any pre-#372 branch still holds the
    retired `CohLean/` and `DGLean/` layouts. Those are a different checkout's
    tracked files, so counting them makes this gate -- and therefore
    `scripts/gates.sh` -- permanently red in any clone that has one, while CI
    stays green because CI checks out clean. A gate that only ever fails locally
    teaches people to ignore it.

    A nested working tree is identified by its own `.git` entry: a directory for
    a clone or submodule, a file for a `git worktree` checkout. Both are pruned.
    """
    for dirpath, dirnames, filenames in os.walk(root):
        here = pathlib.Path(dirpath)
        dirnames[:] = sorted(
            name
            for name in dirnames
            if name not in SKIP_DIRS and not (here / name / ".git").exists()
        )
        for name in sorted(filenames):
            if name.endswith(".lean"):
                yield here / name


def main() -> int:
    failures: list[str] = []

    for path in FORBIDDEN_PATHS:
        if path.exists():
            failures.append(f"retired path exists: {path.relative_to(ROOT)}")

    lean_files = list(lean_sources(ROOT))
    if not lean_files:
        failures.append("no Lean sources found; run the gate from a repository checkout")

    for path in lean_files:
        for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            match = IMPORT.match(line)
            if match and is_forbidden_module(match.group(1)):
                failures.append(
                    f"{path.relative_to(ROOT)}:{line_number}: forbidden import "
                    f"{match.group(1)}"
                )

    lakefile = (ROOT / "lakefile.toml").read_text(encoding="utf-8")
    if re.search(r"(?m)^\s*\[\[lean_lib\]\]\s*$[\s\S]*?^\s*name\s*=\s*"
                 r"[\"']BridgelandStability[\"']", lakefile):
        failures.append("lakefile.toml declares the retired external library root")

    if failures:
        print("source-independence gate failed:")
        for failure in failures:
            print(f"  - {failure}")
        return 1

    print(
        f"ok: {len(lean_files)} Lean sources have zero imports from retired "
        "source and bridge roots"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
