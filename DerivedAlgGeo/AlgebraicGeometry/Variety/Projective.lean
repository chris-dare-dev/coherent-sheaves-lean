/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Variety.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Projective varieties

`Variety/Basic.lean` says in as many words that this repository has no projective variety:

> Mathlib currently has proper and smooth morphisms but no general projective-morphism API. The
> `SmoothProperVariety` bundle below therefore records the geometric hypotheses currently
> expressible without pretending that properness is the definition of projectivity. A later
> projective bundle should extend `Variety` with genuine projective data.

This file supplies that bundle. A `ProjectiveVariety k` is a `Variety k` together with a finite
variable set, a closed immersion into the `Proj` of the standard graded polynomial ring on those
variables, and the compatibility making the immersion a morphism over `Spec k`.

## Properness is derived here, not assumed

`SmoothProperVariety` takes properness as a *field*, because nothing in the tree produced it.
Here it is a theorem: `Proj.toSpecZero` is proper once the graded ring is of finite type over its
degree-zero part, a closed immersion is finite and hence proper, and properness is stable under
composition. That is the direction the two structures should differ in — a projective variety is
proper *because* it is projective — and it is why `ProjectiveVariety` does not extend
`SmoothProperVariety`.

## The degree-zero identification is a construction, not a coincidence

`Proj.toSpecZero 𝒜` lands in `Spec (𝒜 0)`, and for the standard grading `𝒜 0` is the submodule
of degree-zero homogeneous polynomials — not `k` on the nose. `homogeneousZeroRingEquiv` is the
identification, built from `MvPolynomial.C` and inverted by `constantCoeff`, and every statement
below that mentions the base field passes through it explicitly rather than through a defeq that
happens to fire.

## Naming

The grading used here is `MvPolynomial.homogeneousSubmodule ι k`, which is by definition
`AlgebraicGeometry.Proj.polynomialGrading ι k` from `Proj/Modules/Finiteness.lean`. The Mathlib
spelling is used so that the variety layer does not import the Proj Čech-comparison stack; the
two are the same term, so statements in either spelling compose.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

section PolynomialGrading

variable (ι : Type u) (R : Type u) [CommRing R]

/-- The base ring is the degree-zero part of the standard graded polynomial ring.

Both directions are ring homomorphisms already: `MvPolynomial.C` on the way in, and
`MvPolynomial.constantCoeff` on the way out. What needs proof is that they are mutually inverse
*on the degree-zero submodule* — a degree-zero homogeneous polynomial is a constant, which is
`MvPolynomial.totalDegree_eq_zero_iff_eq_C` read through
`MvPolynomial.totalDegree_zero_iff_isHomogeneous`. -/
noncomputable def homogeneousZeroRingEquiv :
    R ≃+* ↥(MvPolynomial.homogeneousSubmodule ι R 0) where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C _ _⟩
  invFun p := MvPolynomial.constantCoeff p.1
  left_inv r := by simp
  right_inv p := by
    refine Subtype.ext ?_
    have hp : (p : MvPolynomial ι R).totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous ι).2
        ((MvPolynomial.mem_homogeneousSubmodule _ _).1 p.2)
    have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 hp
    show MvPolynomial.C (MvPolynomial.constantCoeff (p : MvPolynomial ι R)) = _
    rw [MvPolynomial.constantCoeff_eq]
    exact hc.symm
  map_mul' _ _ := by ext; simp
  map_add' _ _ := by ext; simp

/-- The identification is `MvPolynomial.C` underneath, which is what makes it usable as a rewrite
in statements phrased on the polynomial ring rather than on the degree-zero submodule. -/
@[simp]
lemma homogeneousZeroRingEquiv_apply_coe (r : R) :
    ((homogeneousZeroRingEquiv ι R r : ↥(MvPolynomial.homogeneousSubmodule ι R 0)) :
      MvPolynomial ι R) = MvPolynomial.C r :=
  rfl

/-- The tower `R → 𝒜₀ → R[ι]`. Both algebra structures are Mathlib's —
`SetLike.GradeZero.instAlgebra` on the way in, the subobject coercion on the way out — so the
tower is `rfl`; it is only missing because Mathlib does not register it for grade-zero parts in
general. Local: the finite-type transfer below is its only consumer. -/
local instance isScalarTower_homogeneousZero :
    IsScalarTower R ↥(MvPolynomial.homogeneousSubmodule ι R 0) (MvPolynomial ι R) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := ↥(MvPolynomial.homogeneousSubmodule ι R 0))
    (A := MvPolynomial ι R) rfl

/-- The polynomial ring is of finite type over its degree-zero part when the variable set is
finite. This is what `Proj.toSpecZero`'s properness instance asks for, and it is the only place
the finiteness of the variable set is used. -/
instance finiteType_homogeneousZero [Finite ι] :
    Algebra.FiniteType ↥(MvPolynomial.homogeneousSubmodule ι R 0) (MvPolynomial ι R) :=
  Algebra.FiniteType.of_restrictScalars_finiteType R _ _

end PolynomialGrading

section ProjectiveSpace

variable (ι : Type u) (k : Type u) [Field k]

/-- Projective space over `k` on the variable set `ι`, as the `Proj` of the standard graded
polynomial ring. -/
noncomputable abbrev projectiveSpace : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule ι k)

/-- The structure morphism of projective space to `Spec k`: Mathlib's `Proj.toSpecZero`, followed
by the identification of `k` with the degree-zero part. -/
noncomputable def projectiveSpaceToSpec :
    projectiveSpace ι k ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero _ ≫
    Spec.map (CommRingCat.ofHom (homogeneousZeroRingEquiv ι k).toRingHom)

instance isProper_projectiveSpaceToSpec [Finite ι] : IsProper (projectiveSpaceToSpec ι k) := by
  have : IsIso (CommRingCat.ofHom (homogeneousZeroRingEquiv ι k).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (homogeneousZeroRingEquiv ι k).bijective
  show IsProper (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule ι k) ≫
    Spec.map (CommRingCat.ofHom (homogeneousZeroRingEquiv ι k).toRingHom))
  infer_instance

end ProjectiveSpace

/-- A projective variety over `k`: a variety with a closed immersion into a projective space over
`k`, compatible with the two structure morphisms.

The variable set is data rather than a natural number because the ambient projective space is
`Proj` of a polynomial ring on an index *type*, which is how the Proj lane in this repository
states everything else. `Finite ι` is what makes the ambient space proper, and it is an instance
field so that the properness instance below fires without an explicit argument. -/
structure ProjectiveVariety (k : Type u) [Field k] extends Variety k where
  /-- The homogeneous coordinates of the ambient projective space. -/
  index : Type u
  /-- Finitely many of them. -/
  [finiteIndex : Finite index]
  /-- The projective embedding. -/
  embedding : toVariety.toScheme ⟶ projectiveSpace index k
  /-- It is a closed immersion: this is the projectivity, and it is data. -/
  [isClosedImmersion : IsClosedImmersion embedding]
  /-- The embedding is a morphism over the base field. -/
  overBase : embedding ≫ projectiveSpaceToSpec index k = toVariety.structureMorphism

namespace ProjectiveVariety

variable {k : Type u} [Field k]

attribute [instance] finiteIndex isClosedImmersion

instance instFiniteIndex (X : ProjectiveVariety k) : Finite X.index := X.finiteIndex

instance instIsClosedImmersionEmbedding (X : ProjectiveVariety k) :
    IsClosedImmersion X.embedding := X.isClosedImmersion

/-- A projective variety is proper over the base field.

Not a field of the structure, and not an appeal to a projective-morphism API that does not exist:
the closed immersion is finite hence proper, the ambient projective space is proper over `Spec k`
because the polynomial ring is of finite type over its degree-zero part, and `overBase` says the
structure morphism *is* their composite. -/
instance isProper_structureMorphism (X : ProjectiveVariety k) :
    IsProper X.toVariety.structureMorphism := by
  rw [← X.overBase]
  infer_instance

/-- A projective variety is Noetherian: finite type gives local Noetherianity and properness gives
quasi-compactness over the compact point `Spec k`. -/
noncomputable instance isNoetherian (X : ProjectiveVariety k) :
    IsNoetherian X.toVariety.toScheme where
  toIsLocallyNoetherian := inferInstance
  toCompactSpace :=
    QuasiCompact.compactSpace_of_compactSpace X.toVariety.structureMorphism

/-- A projective variety is separated as an absolute scheme. -/
instance isSeparated (X : ProjectiveVariety k) : X.toVariety.toScheme.IsSeparated where
  isSeparated_terminal_from := by
    rw [← CategoryTheory.Limits.terminal.comp_from X.toVariety.structureMorphism]
    infer_instance

end ProjectiveVariety

end AlgebraicGeometry
