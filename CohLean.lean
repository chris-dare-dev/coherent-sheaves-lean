/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.Numerical.Defs
import CohLean.Numerical.OfGradedBasis
import CohLean.Numerical.RiemannRoch
import CohLean.Numerical.Surface
import CohLean.Numerical.K3
import CohLean.Numerical.Examples.Point
import CohLean.Numerical.Examples.K3Model
import CohLean.Coh.Defs

/-!
# CohLean

Coherent sheaves, Chern classes and Riemann–Roch for smooth projective varieties over a
field, in Lean 4.

* `CohLean.Numerical.*` — **Layer A**, the numerical interface (axioms, no schemes).
* `CohLean.Coh.*` — **Layer B**, the construction from Mathlib's scheme theory.

See `README.md` for the architecture and `ROADMAP.md` for the stage plan.
-/
