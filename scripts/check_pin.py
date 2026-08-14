#!/usr/bin/env python3
"""Assert pins.json matches what this working tree actually resolves.

HARD GATE (exit 1): lean_toolchain and mathlib_rev/mathlib_input_rev in pins.json
must equal lean-toolchain and the mathlib entry of lake-manifest.json. Also checks
mfc_rev when pins.json records it.

ADVISORY (exit 0, prints WARN): cross_repo.status. `ALIGNED` and `MERGED` both
satisfy the single-pin premise. A DIVERGED peer blocks that premise but does
not fail this repo's build. Past
cross_repo.divergence_until it is reported as OVERDUE, still exit 0 -- escalation
is a human decision, not a build break.

Usage:  python3 scripts/check_pin.py [repo_root]
"""

import json
import pathlib
import sys
from datetime import date

root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else __file__).resolve()
if root.is_file():
    root = root.parent.parent

pins_path = root / "pins.json"
if not pins_path.exists():
    print(f"FAIL  no pins.json at {pins_path}")
    sys.exit(1)

pins = json.loads(pins_path.read_text())
manifest = json.loads((root / "lake-manifest.json").read_text())
toolchain = (root / "lean-toolchain").read_text().strip()

packages = {p.get("name"): p for p in manifest.get("packages", [])}
failures = []


def check(label, expected, actual):
    if expected != actual:
        failures.append(f"{label}: pins.json says {expected!r}, tree resolves {actual!r}")


check("lean_toolchain", pins["lean_toolchain"], toolchain)

mathlib = packages.get("mathlib")
if mathlib is None:
    failures.append("mathlib absent from lake-manifest.json")
else:
    check("mathlib_rev", pins["mathlib_rev"], mathlib.get("rev"))
    check("mathlib_input_rev", pins["mathlib_input_rev"], mathlib.get("inputRev"))

for key, pkg in (("mfc_rev", "MathFormalContract"),):
    expected = pins.get(key)
    if expected is None:
        if pkg in packages:
            failures.append(f"{key} is null in pins.json but {pkg} is in the manifest")
    elif pkg not in packages:
        failures.append(f"{key} is {expected!r} but {pkg} is absent from the manifest")
    else:
        check(key, expected, packages[pkg].get("rev"))

if failures:
    print(f"FAIL  {pins['repo']} pin coherence ({len(failures)} problem(s)):")
    for f in failures:
        print(f"  - {f}")
    print("\nFix by re-recording pins.json from this tree, or by correcting the pin.")
    sys.exit(1)

print(f"OK    {pins['repo']} pins match the tree ({toolchain}, mathlib {pins['mathlib_rev'][:12]})")

cross = pins.get("cross_repo") or {}
status = cross.get("status")
if status and status not in {"ALIGNED", "MERGED"}:
    until = cross.get("divergence_until")
    overdue = ""
    if until and date.fromisoformat(until) < date.today():
        overdue = f" -- OVERDUE since {until}"
    print(
        f"WARN  cross-repo {status}{overdue}: peer {cross.get('peer')} is on "
        f"{cross.get('peer_toolchain')} / mathlib {(cross.get('peer_mathlib_rev') or '')[:12]}"
    )
    print("      The single-pin trunk premise does not hold while this is DIVERGED.")

sys.exit(0)
