#!/usr/bin/env python3
"""Prevent stable family APIs from regressing to theorem-specific coherence.

The narrow classes remain source-compatible views of the coherent roots, but
new consumers must depend on `HasCoherentDerivedTensor` and
`HasMonoidalDerivedPullback`. This gate rejects legacy capability assumptions
outside the two compatibility declarations that define the old pulled-unit
views. Geometric family implementations are owned by AlgebraicGeometry.
"""

from __future__ import annotations

import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parent.parent
GEOMETRIC_FAMILIES = (
    ROOT
    / "DerivedAlgGeo"
    / "AlgebraicGeometry"
    / "StabilityCondition"
    / "Families"
)

FORBIDDEN_ASSUMPTIONS = (
    "[HasDerivedTensorAssoc ",
    "[HasDerivedPullbackTensor ",
    "[HasUnitPullbackRightUnitor ",
    "[HasUnitPullbackLeftUnitor ",
)


def main() -> int:
    failures: list[str] = []
    unit_compatibility_lines = 0

    for path in sorted(GEOMETRIC_FAMILIES.rglob("*.lean")):
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), 1
        ):
            stripped = line.strip()
            for token in FORBIDDEN_ASSUMPTIONS:
                if token in line:
                    failures.append(
                        f"{path.relative_to(ROOT)}:{line_number}: "
                        f"legacy coherence assumption {token.strip()}"
                    )

            if "[HasTensorUnit " not in line:
                continue
            if (
                path.name == "KernelUnitConvolution.lean"
                and stripped == "[HasTensorUnit U] where"
            ):
                unit_compatibility_lines += 1
                continue
            failures.append(
                f"{path.relative_to(ROOT)}:{line_number}: legacy tensor-unit "
                "assumption outside its compatibility declaration"
            )

    if unit_compatibility_lines != 2:
        failures.append(
            "expected exactly two pulled-unit compatibility declarations; "
            f"found {unit_compatibility_lines}"
        )

    if failures:
        print("coherent-families gate failed:")
        for failure in failures:
            print(f"  - {failure}")
        return 1

    print(
        "ok: stable family consumers use coherent tensor and monoidal "
        "pullback roots"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
