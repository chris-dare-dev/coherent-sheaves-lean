/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.Numerical.Defs
import CohLean.Numerical.OfGradedBasis
import CohLean.Numerical.RiemannRoch
import CohLean.Numerical.Surface
import CohLean.Numerical.Threefold
import CohLean.Numerical.Fourfold
import CohLean.Numerical.K3
import CohLean.Numerical.Dual
import CohLean.Numerical.EulerPairing
import CohLean.Numerical.Examples.Point
import CohLean.Numerical.Examples.RankOneSurface
import CohLean.Numerical.Examples.K3Model
import CohLean.Numerical.Examples.ProjectivePlaneModel
import CohLean.ForMathlib.PresentationIsFinite
import CohLean.ForMathlib.FinitePresentationOfPresentation
import CohLean.ForMathlib.OpensLimits
import CohLean.ForMathlib.AffineComparison
import CohLean.ForMathlib.ToSheafExact
import CohLean.AlgebraicGeometry.Modules.RestrictOver
import CohLean.AlgebraicGeometry.Modules.ModulesEquiv
import CohLean.Coh.Defs
import CohLean.Coh.ClosedUnderIso
import CohLean.Coh.Local
import CohLean.Coh.Affine
import CohLean.Cohomology.Strategy

/-!
# CohLean

Coherent sheaves, Chern classes and Riemann–Roch for smooth projective varieties over a
field, in Lean 4.

* `CohLean.Numerical.*` — **Layer A**, the numerical interface (axioms, no schemes).
* `CohLean.Coh.*` — **Layer B**, the construction from Mathlib's scheme theory.

See `README.md` for the architecture and `ROADMAP.md` for the stage plan.
-/
