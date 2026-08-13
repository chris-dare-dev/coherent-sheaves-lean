#!/usr/bin/env python3
"""Assert that designated modules never reach `BridgelandStability` on their import path.

Import-level, not declaration-level: a module is tainted if it imports the anchor
directly, or imports any repo-local module that is itself tainted. This is the
stronger of the two rules, and it is the one that can be checked mechanically.

Run:

    python3 scripts/check_anchor_free.py

Exit status 0 if every module listed in ANCHOR_FREE is clean, 1 otherwise.
"""

from __future__ import annotations

import os
import re
import sys
from collections import defaultdict

ROOT = "BridgelandStabLean"
ANCHOR = "BridgelandStability"

# Modules that must never reach the anchor. Add to this list, never remove from it
# without a stated reason -- each entry is a boundary someone paid to establish.
ANCHOR_FREE = [
    "BridgelandStabLean.TStructure",
    "BridgelandStabLean.TStructure.Exactness",
    "BridgelandStabLean.ForMathlib.CategoryTheory.ObjectProperty.FullSubcategory",
    "BridgelandStabLean.ForMathlib.CategoryTheory.Triangulated.TStructure.HeartAbelian",
    "BridgelandStabLean.StabilityCondition.Weak.Tilting.Cohomology.Basic",
    "BridgelandStabLean.StabilityCondition.Weak.Tilting.Cohomology.Homological",
    "BridgelandStabLean.StabilityCondition.Weak.Tilting.Cohomology.Exactness",
    "BridgelandStabLean.StabilityCondition.Weak.Tilting.TorsionPair.Basic",
    "BridgelandStabLean.StabilityCondition.Weak.Tilting.TorsionPair.Heart",
]

IMPORT = re.compile(r"^import\s+(\S+)")


def module_map() -> dict[str, str]:
    mods: dict[str, str] = {}
    for dirpath, _, filenames in os.walk(ROOT):
        for name in filenames:
            if name.endswith(".lean"):
                path = os.path.join(dirpath, name)
                mods[path[: -len(".lean")].replace(os.sep, ".")] = path
    return mods


def main() -> int:
    mods = module_map()
    if not mods:
        print(f"error: no .lean files under {ROOT}/ -- wrong working directory?")
        return 1

    local_imports: dict[str, list[str]] = defaultdict(list)
    direct_anchor: set[str] = set()

    for module, path in mods.items():
        with open(path, encoding="utf-8") as handle:
            for line in handle:
                match = IMPORT.match(line)
                if not match:
                    continue
                target = match.group(1)
                if target.split(".")[0] == ANCHOR:
                    direct_anchor.add(module)
                elif target in mods:
                    local_imports[module].append(target)

    memo: dict[str, list[str] | None] = {}

    def path_to_anchor(module: str, stack: tuple[str, ...] = ()) -> list[str] | None:
        """Return a witness import chain reaching the anchor, or None if clean."""
        if module in memo:
            return memo[module]
        if module in direct_anchor:
            memo[module] = [module]
            return memo[module]
        if module in stack:  # import cycles are a Lean error; do not recurse forever
            return None
        result = None
        for dependency in local_imports[module]:
            witness = path_to_anchor(dependency, stack + (module,))
            if witness is not None:
                result = [module] + witness
                break
        memo[module] = result
        return result

    failures = 0
    for module in ANCHOR_FREE:
        if module not in mods:
            print(f"FAIL {module}\n     module does not exist -- stale entry in ANCHOR_FREE")
            failures += 1
            continue
        witness = path_to_anchor(module)
        if witness is None:
            print(f"ok   {module}")
        else:
            failures += 1
            print(f"FAIL {module}")
            print("     reaches the anchor via:")
            for step in witness:
                print(f"       {step}")

    if failures:
        print(f"\n{failures} module(s) reach {ANCHOR}. See the chain above.")
        return 1
    print(f"\nAll {len(ANCHOR_FREE)} module(s) are anchor-free at import level.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
