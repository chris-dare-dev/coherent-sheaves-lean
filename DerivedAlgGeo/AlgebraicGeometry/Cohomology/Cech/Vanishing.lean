/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.CechPrimitive
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.ProjectiveSpace

/-!
# `Hⁿ(Pⁿ, O(d)) = 0` for `n ≥ 1` and `d ≥ 0`

The headline of #340. Everything difficult happened earlier: the block decomposition, the
contracting homotopy, and the cochain-level computation `cechPrimitive_isPrimitive` that every
positive-degree cocycle of the variable Čech complex is a coboundary. This file only converts:
the cochain statement becomes exactness of the algebraic Čech complex through
`ShortComplex.ab_exact_iff` and `polynomialVariableCechComplex_d_apply`, exactness becomes
vanishing homology, and vanishing homology becomes the vanishing of `Hⁿ(Pⁿ, O(d))` through the
comparison `polynomialVariableCechComplex_computesCohomology` of #495.

The `H⁰` companion is not restated here: degree-zero global sections of `O(d)` are the
degree-`d` homogeneous polynomials by `polynomialTwistingGlobalSectionsModuleIso`, which
remains the canonical statement and is deliberately not reproved.

The `HasExt` witness is passed positionally, as everywhere in this lane: `Sheaf.H` lands in
the `HasExt` universe, and letting instance search pick would allow the small-site
`HasExt.{u}` to name different groups.

## Tags

Čech cohomology, projective space, twisting sheaf, vanishing
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable (ι k : Type u) [Field k]

/-- **The algebraic Čech complex of `O(d)` is exact in every positive degree.** This is the
cochain-level homotopy computation `cechPrimitive_isPrimitive`, read through the coordinate
formula for the differential. -/
theorem polynomialVariableCechComplex_exactAt (d n : ℕ) :
    (polynomialVariableCechComplex ι k d).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1)
    (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1)),
    ShortComplex.ab_exact_iff]
  intro s hs
  let s' : ∀ x : Fin (n + 2) → ι, polynomialVariableCechTerm ι k d (n + 1) x := s
  have hs' : ∀ x : Fin (n + 1 + 2) → ι,
      ∑ j : Fin (n + 1 + 2), (-1 : ℤ) ^ (j : ℕ) •
        polynomialVariableCechFace ι k d x j (s' (x ∘ j.succAbove)) = 0 := by
    intro x
    have hx : ConcreteCategory.hom
        ((polynomialVariableCechComplex ι k d).d (n + 1) (n + 1 + 1)) s' x = 0 :=
      congrArg (fun t => t x) hs
    rwa [polynomialVariableCechComplex_d_apply] at hx
  refine ⟨cechPrimitive ι k d s', ?_⟩
  show ConcreteCategory.hom
      ((polynomialVariableCechComplex ι k d).d n (n + 1)) (cechPrimitive ι k d s') = s
  funext x
  rw [polynomialVariableCechComplex_d_apply]
  exact cechPrimitive_isPrimitive ι k d s' hs' x

/-- The homology of the algebraic Čech complex vanishes in every positive degree. -/
theorem polynomialVariableCechComplex_homology_isZero (d n : ℕ) :
    IsZero ((polynomialVariableCechComplex ι k d).homology (n + 1)) :=
  ((polynomialVariableCechComplex ι k d).exactAt_iff_isZero_homology (n + 1)).mp
    (polynomialVariableCechComplex_exactAt ι k d n)

/-- **`Hⁿ(Pⁿ, O(d)) = 0` for `n ≥ 1` and `d ≥ 0`**, stated as the triviality of the derived
sections group. The twist is a natural number, which is the whole of the `d ≥ 0` hypothesis;
the projective space is `Proj` of a polynomial ring in an arbitrary — possibly infinite —
variable set over a field. -/
theorem polynomialTwisting_H_subsingleton (d n : ℕ)
    [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u}
      (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k)))] :
    Subsingleton
      (@CategoryTheory.Sheaf.H
        (Opens (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k))) _
        (Opens.grothendieckTopology
          (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k)))
        ((_root_.AlgebraicGeometry.Scheme.Modules.toSheaf _).obj
          (associatedSheaf (polynomialGrading ι k)
            (natShift (polynomialGrading ι k) d))) _ hExt (n + 1)) := by
  obtain ⟨e⟩ := polynomialVariableCechComplex_computesCohomology ι k d (n + 1)
  have hsub : Subsingleton
      (((polynomialVariableCechComplex ι k d).homology (n + 1) : AddCommGrpCat.{u})) :=
    AddCommGrpCat.subsingleton_of_isZero
      (polynomialVariableCechComplex_homology_isZero ι k d n)
  exact Equiv.subsingleton e.symm.toEquiv

end AlgebraicGeometry.Proj
