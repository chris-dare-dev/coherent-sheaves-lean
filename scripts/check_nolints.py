#!/usr/bin/env python3
"""Keep `scripts/nolints.json` a ratchet rather than a dumping ground.

`lake exe runLinter DerivedAlgGeo` already rejects any violation that is not listed
in `scripts/nolints.json`, so new code cannot add one. What it cannot detect is
someone silencing a failure with `runLinter --update`, which rewrites the whole
file from the current run and blesses the new violation along with every
existing one. That turns the gate off without touching CI or any Lean file.

This script closes that hole from the other side: the list may shrink, never
grow. The dg-category and stability-condition subsystems entered the unified
library without exceptions and must remain clean.

Usage:
    python3 scripts/check_nolints.py
    python3 scripts/check_nolints.py --relax   # after deliberately shrinking it
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

NOLINTS = Path("scripts/nolints.json")

# The backlog as measured when the algebraic-geometry gate was first wired, 2026-08-14.
# Lower it whenever the real count drops -- `--relax` does that for you. It is
# never raised: a change that needs a new exception needs a human argument for
# that exception, in review, not a bumped constant.
CEILING = 203

# Per-linter ceilings, for the same reason and with more resolution: they catch
# an `--update` run from a library that lints clean today, which would add its
# output here and quietly disable its own gate. Declaration names cannot be used
# for that check -- plenty of genuine project declarations live in Mathlib-rooted
# namespaces like `ModuleCat.` -- but any such update grows a count.
PER_LINTER_CEILING = {
    "docBlame": 148,
    "unusedArguments": 27,
    "defsWithUnderscore": 16,
    "simpNF": 12,
}


def main(argv: list[str]) -> int:
    if not NOLINTS.exists():
        print(f"::error::{NOLINTS} is missing; the DerivedAlgGeo linter gate depends on it")
        return 1

    entries = json.loads(NOLINTS.read_text(encoding="utf-8"))
    by_linter = Counter(linter for linter, _ in entries)
    total = len(entries)

    if "--relax" in argv:
        print(f"set CEILING = {total} and PER_LINTER_CEILING = {dict(sorted(by_linter.items()))}")
        return 0

    print(f"nolints: {total} entries (ceiling {CEILING}) — " +
          ", ".join(f"{k}={v}" for k, v in sorted(by_linter.items())))

    if total > CEILING:
        print(
            f"::error::nolints grew from {CEILING} to {total}. Fix the declaration "
            "instead, or argue for the exception in review — do not resolve a linter "
            "failure with `runLinter --update`."
        )
        return 1

    if total < CEILING:
        print(
            f"note: the backlog shrank by {CEILING - total}. Run with --relax and "
            "lower CEILING so the ratchet holds the new ground."
        )

    grown = {
        linter: (n, PER_LINTER_CEILING.get(linter, 0))
        for linter, n in by_linter.items()
        if n > PER_LINTER_CEILING.get(linter, 0)
    }
    if grown:
        for linter, (now, was) in sorted(grown.items()):
            print(f"::error::{linter} grew from {was} to {now}")
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
