/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.StabilityCondition.Families.Ordinary
import BridgelandStabLean.StabilityCondition.Families.Weak

/-!
# Dependency contract for Theorem 22.2

Theorem 22.2 of arXiv:1902.08184v4 concludes that the relevant stability
space is a complex manifold and that its central-charge map is a local
isomorphism.  Its proof calls on Definition 20.5(2)--(3) and Definition
21.15(4)--(5).  This file packages those four source inputs and separately
names the geometric infrastructure which this repository does not possess.

There is intentionally **no theorem** from `Theorem22_2DependencyContract` to
the complex-manifold/local-isomorphism conclusion.  Such a declaration would
need concrete relative categories, base change, semiorthogonal decompositions,
moduli boundedness, and complex-analytic deformation theory.  Prop-valued
fields below are premises to be implemented by a geometric client; they are
not axioms or claimed results of this library.
-/

namespace BridgelandStabLean.StabilityFamilies

open BridgelandStabLean.Foundation
open BridgelandStabLean.Support

noncomputable section

variable {JOpen D I M V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

private local instance quotientSubmoduleClosed (V₀ : Submodule ℝ V) :
    IsClosed (V₀ : Set V) :=
  V₀.closed_of_finiteDimensional

/-- The four exact source clauses used by the proof of Theorem 22.2.  This is
an input contract, not the theorem's conclusion. -/
structure Theorem22_2SourceClauses
    (stable : JOpen → OpenLocusProbe)
    (dedekind : DedekindHNProblem D)
    (V₀ : Submodule ℝ V) (Z : V →ₗ[ℝ] W)
    (hV₀ : V₀ ≤ LinearMap.ker Z) (semistableClasses : I → Set V)
    (boundedness : BoundednessProblem M) : Prop where
  /-- Definition 20.5(2): universal openness of geometric stability. -/
  openness : UniversalOpenness stable
  /-- Definition 20.5(3): HN integration after every eligible Dedekind base
  change. -/
  dedekindHN : IntegratesAfterDedekindBaseChange dedekind
  /-- Definition 21.15(4): one quadratic form on the real quotient, uniform
  across all fiber semistable classes. -/
  uniformSupport : HasUniformQuadraticSupportPropertyModulo
    V₀ Z hV₀ semistableClasses
  /-- Definition 21.15(5): boundedness of every supplied numerical moduli
  problem. -/
  bounded : UniversalBoundedness boundedness

/-- The complete dependency ledger needed before Theorem 22.2 can honestly be
attempted in this repository.

The first field is the source-level four-clause bundle.  The remaining fields
make the current cross-repository gaps explicit.  In particular, none is
deduced merely from the abstract probes. -/
structure Theorem22_2DependencyContract
    (stable : JOpen → OpenLocusProbe)
    (dedekind : DedekindHNProblem D)
    (V₀ : Submodule ℝ V) (Z : V →ₗ[ℝ] W)
    (hV₀ : V₀ ≤ LinearMap.ker Z) (semistableClasses : I → Set V)
    (boundedness : BoundednessProblem M)
    (RelativeCategoryBaseChange SemiorthogonalBaseChange
      RelativeHNGeometry ModuliGeometry ComplexAnalyticDeformation : Prop) : Prop where
  /-- The four hypotheses cited in the paper's proof. -/
  sourceClauses : Theorem22_2SourceClauses stable dedekind V₀ Z hV₀
    semistableClasses boundedness
  /-- Relative categories and their pullback functors exist and satisfy the
  needed compatibilities. -/
  relativeCategoryBaseChange : RelativeCategoryBaseChange
  /-- The required semiorthogonal decompositions and t-structures survive
  base change. -/
  semiorthogonalBaseChange : SemiorthogonalBaseChange
  /-- Fiberwise HN data is represented by the relative HN structures used in
  the deformation argument. -/
  relativeHNGeometry : RelativeHNGeometry
  /-- The boundedness predicate is realized by the needed moduli geometry. -/
  moduliGeometry : ModuliGeometry
  /-- The complex-analytic deformation and period-map machinery needed for
  the manifold and local-isomorphism conclusion. -/
  complexAnalyticDeformation : ComplexAnalyticDeformation

/-- Project the four cited source clauses from the larger implementation
contract. -/
theorem Theorem22_2DependencyContract.hasSourceClauses
    {stable : JOpen → OpenLocusProbe} {dedekind : DedekindHNProblem D}
    {V₀ : Submodule ℝ V} {Z : V →ₗ[ℝ] W}
    {hV₀ : V₀ ≤ LinearMap.ker Z} {S : I → Set V}
    {boundedness : BoundednessProblem M}
    {RBC SOD RHN Moduli Analytic : Prop}
    (h : Theorem22_2DependencyContract stable dedekind V₀ Z hV₀ S
      boundedness RBC SOD RHN Moduli Analytic) :
    Theorem22_2SourceClauses stable dedekind V₀ Z hV₀ S boundedness :=
  h.sourceClauses

end

end BridgelandStabLean.StabilityFamilies
