#!/usr/bin/env python3
"""Reject every source-level dependency on the retired stability-code source.

This is intentionally a repository-wide zero-import gate.  It has no
allowlist: the retired module root and the two former bridge roots may not be
imported by any tracked Lean source.  It also rejects restoration of the
deleted source/bridge paths or the two exact copied helper files that were
replaced by owner-native proofs.
"""

from __future__ import annotations

import pathlib
import re
import sys


ROOT = pathlib.Path(__file__).resolve().parent.parent
IMPORT = re.compile(r"^\s*import\s+(\S+)")
FORBIDDEN_MODULE_ROOTS = (
    "BridgelandStability",
    "BridgelandStabLean.Anchor",
    "BridgelandStabLean.Compatibility",
)
FORBIDDEN_PATHS = (
    ROOT / "vendor" / "BridgelandStability",
    ROOT / "BridgelandStabLean" / "Anchor.lean",
    ROOT / "BridgelandStabLean" / "Anchor",
    ROOT / "BridgelandStabLean" / "Compatibility.lean",
    ROOT / "BridgelandStabLean" / "Compatibility",
    ROOT
    / "BridgelandStabLean"
    / "ForMathlib"
    / "CategoryTheory"
    / "ObjectProperty"
    / "FullSubcategory.lean",
    ROOT
    / "BridgelandStabLean"
    / "ForMathlib"
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


def main() -> int:
    failures: list[str] = []

    for path in FORBIDDEN_PATHS:
        if path.exists():
            failures.append(f"retired path exists: {path.relative_to(ROOT)}")

    lean_files = [
        path
        for path in ROOT.rglob("*.lean")
        if ".lake" not in path.parts and ".git" not in path.parts
    ]
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
