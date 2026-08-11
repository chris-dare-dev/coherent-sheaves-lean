/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.AlgebraicGeometry.Variety
import CohLean.AlgebraicGeometry.Variety.Numerical
import CohLean.Numerical.Defs
import CohLean.Numerical.OfGradedBasis
import CohLean.Numerical.CharacteristicClasses
import CohLean.Numerical.RiemannRoch
import CohLean.Numerical.Discriminant
import CohLean.Numerical.K3
import CohLean.Numerical.Dual
import CohLean.Numerical.EulerPairing
import CohLean.Intersection.NumericalPolynomial
import CohLean.Intersection.Snapper
import CohLean.Intersection.Number
import CohLean.Intersection.ChernCharacterSurface
import CohLean.Numerical.Examples.Point
import CohLean.Numerical.Examples.RankOneSurface
import CohLean.Numerical.Examples.K3Model
import CohLean.Numerical.Examples.ProjectivePlaneModel
import CohLean.AlgebraicGeometry.Modules.PresentationIsFinite
import CohLean.AlgebraicGeometry.Modules.FinitePresentationOfPresentation
import CohLean.Topology.Opens.Limits
import CohLean.Topology.Opens.CoversTop
import CohLean.AlgebraicGeometry.Modules.AffineComparison
import CohLean.AlgebraicGeometry.Modules.QuasicoherentBasicOpen
import CohLean.AlgebraicGeometry.Modules.AffineComparisonGluing
import CohLean.AlgebraicGeometry.Modules.AffineComparisonFiniteness
import CohLean.AlgebraicGeometry.Modules.ToSheafExact
import CohLean.Cohomology.Simplicial.ExtraCodegeneracy
import CohLean.Cohomology.SpectralSequence.FilteredComplexSpectralObject
import CohLean.Cohomology.SpectralSequence.FilteredTotalComplex
import CohLean.Cohomology.SpectralSequence.FilteredTotalComplexAdjacent
import CohLean.Cohomology.SpectralSequence.FilteredTotalComplexFirstPageDifferential
import CohLean.Cohomology.SpectralSequence.TotalQuasiIso
import CohLean.Divisors.Cartier
import CohLean.Divisors.Picard
import CohLean.Divisors.Tensor
import CohLean.Divisors.Monoidal
import CohLean.Divisors.Symmetric
import CohLean.Divisors.PicardGroup
import CohLean.Divisors.AssociatedSheaf
import CohLean.AlgebraicGeometry.Modules.RestrictOver
import CohLean.AlgebraicGeometry.Modules.ModulesEquiv
import CohLean.Coh.Defs
import CohLean.Coh.ClosedUnderIso
import CohLean.Coh.Local
import CohLean.Coh.Affine
import CohLean.Coh.Kernels
import CohLean.Coh.Extensions
import CohLean.Coh.Abelian
import CohLean.Divisors.Effective
import CohLean.Divisors.Determinant
import CohLean.Cohomology.AffineCech
import CohLean.Cohomology.CechBicomplex
import CohLean.Cohomology.CechComparison
import CohLean.Cohomology.InjectiveFlasque
import CohLean.Cohomology.FreeAbelianYonedaStalk
import CohLean.Cohomology.InjectiveCechAcyclic
import CohLean.Cohomology.CechInitialPage
import CohLean.Cohomology.CechTotalComparison
import CohLean.Cohomology.EulerCharacteristic
import CohLean.Cohomology.EulerCharacteristicAdditivity
import CohLean.Cohomology.Strategy

/-!
# CohLean

Coherent sheaves, Chern classes and Riemann–Roch for smooth projective varieties over a
field, in Lean 4.

* `CohLean.Numerical.*` — the dimension-general numerical interface (axioms, no schemes).
* `CohLean.AlgebraicGeometry.*`, `CohLean.Coh.*`, and `CohLean.Divisors.*` — geometric
  constructions built over Mathlib's scheme theory.
* `CohLean.Intersection.*` — numerical-polynomial and intersection machinery connecting the
  geometric and numerical layers.
* `CohLean.Topology.*` and `CohLean.Cohomology.*` — permanent project infrastructure,
  replaced by Mathlib declarations only when equivalent APIs become available.

See `README.md` for the architecture and `ROADMAP.md` for the stage plan.
-/
