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
    "BridgelandStabLean.Foundation",
    "BridgelandStabLean.Foundation.PostnikovTower",
    "BridgelandStabLean.Foundation.Slicing",
    "BridgelandStabLean.Foundation.GrothendieckPresentation",
    "BridgelandStabLean.Foundation.TriangulatedGrothendieck",
    "BridgelandStabLean.Foundation.TriangulatedGrothendieckFunctorial",
    "BridgelandStabLean.Foundation.PreStabilityCondition",
    "BridgelandStabLean.Foundation.IntervalCategory",
    "BridgelandStabLean.Foundation.StabilityCondition",
    "BridgelandStabLean.Foundation.Deformation.RelativePhase",
    "BridgelandStabLean.Foundation.Deformation.NearIdentity",
    "BridgelandStabLean.Foundation.Deformation.LocalFiniteness",
    "BridgelandStabLean.Foundation.Deformation.PhaseArithmetic",
    "BridgelandStabLean.Foundation.Deformation.SkewedStability",
    "BridgelandStabLean.Foundation.Deformation.ChargePerturbation",
    "BridgelandStabLean.Foundation.Deformation.StabilitySeminorm",
    "BridgelandStabLean.Foundation.Slicing.PhaseBounds",
    "BridgelandStabLean.Foundation.Slicing.FiltrationOperations",
    "BridgelandStabLean.Foundation.Slicing.PhaseTruncation",
    "BridgelandStabLean.Foundation.StabilityFunction.Basic",
    "BridgelandStabLean.Foundation.StabilityFunction.HarderNarasimhan",
    "BridgelandStabLean.Foundation.StabilityFunction.Subobject",
    "BridgelandStabLean.Foundation.StabilityFunction.PhaseGeometry",
    "BridgelandStabLean.Foundation.StabilityFunction.Uniqueness",
    "BridgelandStabLean.TStructure",
    "BridgelandStabLean.TStructure.Exactness",
    "BridgelandStabLean.TStructure.Shift",
    "BridgelandStabLean.ForMathlib.CategoryTheory.ObjectProperty.FullSubcategory",
    "BridgelandStabLean.ForMathlib.CategoryTheory.Triangulated.TStructure.HeartAbelian",
    "BridgelandStabLean.StabilityCondition.Weak.Tilting.Cohomology.Basic",
    "BridgelandStabLean.StabilityCondition.Weak.Tilting.Cohomology.Homological",
    "BridgelandStabLean.StabilityCondition.Weak.Tilting.Cohomology.Exactness",
    "BridgelandStabLean.StabilityCondition.Weak.Tilting.TorsionPair.Basic",
    "BridgelandStabLean.StabilityCondition.Weak.Tilting.TorsionPair.Heart",
]

# The ownership migration starts with 27 historical owner modules that import
# the vendor directly, plus the one explicit compatibility boundary introduced
# by issue #226.  This allowlist may only shrink outside Compatibility/: a new
# direct import would spread the third-party boundary and is therefore an error.
DIRECT_ANCHOR_ALLOWLIST = {
    "BridgelandStabLean.Anchor.TStructure",
    "BridgelandStabLean.Compatibility.BridgelandStability",
    "BridgelandStabLean.StabilityCondition.Metric.Distance.Topology",
    "BridgelandStabLean.StabilityCondition.Metric.Isometry.Phase",
    "BridgelandStabLean.StabilityCondition.Metric.Mass.Subadditivity.CohomologyExactness",
    "BridgelandStabLean.StabilityCondition.Metric.Mass.Subadditivity.HNPolygon",
    "BridgelandStabLean.StabilityCondition.Metric.Mass.Subadditivity.Triangle",
    "BridgelandStabLean.StabilityCondition.Metric.Mass.Uniqueness",
    "BridgelandStabLean.StabilityCondition.Phase.Order.Basic",
    "BridgelandStabLean.StabilityCondition.Phase.Transfer.Basic",
    "BridgelandStabLean.StabilityCondition.Symmetry.Autoequivalence.Foundations.FiniteLength",
    "BridgelandStabLean.StabilityCondition.Symmetry.Autoequivalence.Foundations.GrothendieckGroup",
    "BridgelandStabLean.StabilityCondition.Symmetry.Autoequivalence.Slicing.Transport",
    "BridgelandStabLean.StabilityCondition.Symmetry.Autoequivalence.Stability.ClassMap",
    "BridgelandStabLean.StabilityCondition.Symmetry.Autoequivalence.Stability.Transport",
    "BridgelandStabLean.StabilityCondition.Symmetry.Combined.Components",
    "BridgelandStabLean.StabilityCondition.Symmetry.Combined.Effective",
    "BridgelandStabLean.StabilityCondition.Symmetry.Combined.Topology",
    "BridgelandStabLean.StabilityCondition.Symmetry.GLTilde.Action.PreStability",
    "BridgelandStabLean.StabilityCondition.Symmetry.GLTilde.Action.Slicing",
    "BridgelandStabLean.StabilityCondition.Symmetry.GLTilde.Action.Stability",
    "BridgelandStabLean.StabilityCondition.Weak.Basic.Definitions",
    "BridgelandStabLean.StabilityCondition.Weak.Foundations.SimpleCharge",
    "BridgelandStabLean.StabilityCondition.Weak.Heart.Equivalence",
    "BridgelandStabLean.StabilityCondition.Weak.Heart.EquivalenceReverse",
    "BridgelandStabLean.StabilityCondition.Weak.Heart.Noetherian",
    "BridgelandStabLean.StabilityCondition.Weak.Tilting.Cohomology.Sequence",
    "BridgelandStabLean.StabilityCondition.Weak.Tilting.TorsionPair.Slope",
}

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
    unexpected_direct = direct_anchor - DIRECT_ANCHOR_ALLOWLIST
    stale_direct = DIRECT_ANCHOR_ALLOWLIST - direct_anchor
    for module in sorted(unexpected_direct):
        print(f"FAIL {module}\n     new direct import of {ANCHOR} is not allowlisted")
        failures += 1
    for module in sorted(stale_direct):
        print(f"FAIL {module}\n     stale direct-import allowlist entry; remove it after migration")
        failures += 1

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
    print(f"Direct {ANCHOR} imports are frozen at {len(direct_anchor)} allowlisted modules.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
