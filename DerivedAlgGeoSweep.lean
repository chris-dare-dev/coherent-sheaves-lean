/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/

import DerivedAlgGeo
import DerivedAlgGeo.Development

/-!
# The sweep umbrella

The module `lake exe emit` imports. It exists only so that the emitter's
environment contains **every tracked Lean module in this repository**, and it
declares nothing itself.

## Why this is not `DerivedAlgGeo.lean`

`DerivedAlgGeo.lean` is the public mathematical library. Development probes
are deliberately excluded from that API, but the `sorry` gate must still see
them. The sweep root imports the public umbrella and those probes.

## Why an import here is load-bearing

`MathFormalContract.emitToFileForRootsImpl` builds its environment with
`importModules #[{ module := rootLib }]`. The `additionalRoots` argument widens
the *scope filter*, not the *import*: a module named there but not reachable by
import from `rootLib` contributes no constants, and the emitter reports a
smaller sweep with exit code 0. Measured before this module existed, the
emission covered 406 of 419 tracked modules — the dg-category development,
development probes, and the former vendor umbrella were absent, and nothing
said so. Those maintained results are now all reachable through
`DerivedAlgGeo` and `DerivedAlgGeo.Development`.

Adding a library root to `lakefile.toml` is therefore not enough to gate it.
Import it here as well, and add it to `additionalRoots` in `exe/Emit.lean` if
it is not already below one of the roots listed there.
`scripts/check_emission_coverage.py` fails when a tracked module is missing
from the emission, so this is enforced rather than remembered.
-/
