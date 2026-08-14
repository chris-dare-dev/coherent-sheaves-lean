/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/

import DerivedAlgGeoLean
import DGLean
import CohLean.Development

/-!
# The sweep umbrella

The module `lake exe emit` imports. It exists only so that the emitter's
environment contains **every tracked Lean module in this repository**, and it
declares nothing itself.

## Why this is not `DerivedAlgGeoLean.lean`

`CLAUDE.md` keeps that umbrella limited to stable library roots, and `DGLean`
is deliberately outside it until the seam theorem of `dg-enhancements-e4`.
Those are statements about what the *library* offers a downstream user. The
`sorry` gate has the opposite obligation: it must cover code precisely because
it is unstable, and it must cover code nothing imports. Widening the stable
umbrella to serve the gate would trade a real API boundary for a build detail.
So the gate gets its own root, and the two obligations stop competing.

## Why an import here is load-bearing

`MathFormalContract.emitToFileForRootsImpl` builds its environment with
`importModules #[{ module := rootLib }]`. The `additionalRoots` argument widens
the *scope filter*, not the *import*: a module named there but not reachable by
import from `rootLib` contributes no constants, and the emitter reports a
smaller sweep with exit code 0. Measured before this module existed, the
emission covered 406 of 419 tracked modules — all of `DGLean`, all of
`CohLean.Development`, and the former vendor umbrella were absent, and nothing
said so. The vendor root has since been retired; its surviving maintained
results are reachable through `BridgelandStabLean`.

Adding a library root to `lakefile.toml` is therefore not enough to gate it.
Import it here as well, and add it to `additionalRoots` in `exe/Emit.lean` if
it is not already below one of the roots listed there.
`scripts/check_emission_coverage.py` fails when a tracked module is missing
from the emission, so this is enforced rather than remembered.
-/
