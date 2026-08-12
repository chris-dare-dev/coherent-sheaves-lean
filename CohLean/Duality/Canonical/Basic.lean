/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.AlgebraicGeometry.Divisors.AssociatedSheaf
import CohLean.AlgebraicGeometry.Divisors.Determinant
import CohLean.AlgebraicGeometry.Variety.Basic
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf

/-!
# Canonical sheaf data and the duality construction boundary

For a smooth variety of pure relative dimension `n`, the canonical sheaf is the determinant of
the relative cotangent sheaf. This file packages that construction using CohLean's existing
fixed-rank locally-free and determinant interfaces, and exposes its Picard and Cartier-divisor
classes.

The companion `Canonical.Differentials` and `Canonical.Descent` modules construct the relative
cotangent sheaf, its fixed-rank atlas, its top exterior power, and an explicit sheaf-dual tensor
inverse. Consequently `CanonicalSheafData.ofSmoothRelativeDimension` builds this package from
smooth pure relative dimension alone. The structure remains useful as an explicit interface for
downstream constructions and alternative cotangent models. It does not postulate Serre duality as
an axiom: `Canonical.Derived` constructs only the derived-category object `ω_X[n]`, while
`DualizingSheafComparison` merely compares a separately constructed candidate with the canonical
sheaf.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace SmoothProperVariety

variable {k : Type u} [Field k] (X : SmoothProperVariety k)

/-- Explicit canonical-sheaf construction data on a smooth proper variety of pure dimension `n`.

`ofSmoothRelativeDimension` constructs these fields canonically from the genuine Mathlib
relative-dimension morphism property; retaining the fields keeps the interface open to alternative
cotangent and determinant models. -/
structure CanonicalSheafData (n : ℕ) where
  /-- The structure morphism is smooth of pure relative dimension `n`. -/
  smoothOfRelativeDimension :
    SmoothOfRelativeDimension n X.toVariety.structureMorphism
  /-- The chosen relative cotangent module sheaf. -/
  cotangent : X.toVariety.toScheme.Modules
  /-- Fixed-rank and determinant data for the chosen cotangent sheaf. -/
  cotangentDeterminant : Scheme.Modules.DeterminantData cotangent
  /-- Its locally free rank agrees with the geometric relative dimension. -/
  cotangent_rank : cotangentDeterminant.rank = n

namespace CanonicalSheafData

variable {X} {n : ℕ} (C : CanonicalSheafData X n)

/-- The canonical line bundle, defined as the determinant of the cotangent sheaf. -/
noncomputable abbrev canonicalLineBundle :
    Scheme.Modules.LineBundleData X.toVariety.toScheme :=
  C.cotangentDeterminant.topExteriorPower

/-- The underlying canonical module sheaf `ω_X`. -/
noncomputable abbrev canonicalSheaf : X.toVariety.toScheme.Modules :=
  C.canonicalLineBundle.line

/-- The inverse, or anticanonical, line bundle. -/
noncomputable def antiCanonicalLineBundle :
    Scheme.Modules.LineBundleData X.toVariety.toScheme :=
  C.canonicalLineBundle.dual

/-- The canonical Picard class `[ω_X]`. -/
noncomputable def canonicalClass : Scheme.Modules.Pic X.toVariety.toScheme :=
  C.canonicalLineBundle.toPic

/-- The canonical class in additive notation. -/
noncomputable def canonicalClassAdd : Additive (Scheme.Modules.Pic X.toVariety.toScheme) :=
  Additive.ofMul C.canonicalClass

/-- The anticanonical Picard class is the inverse of the canonical class. -/
@[simp]
theorem antiCanonicalClass :
    C.antiCanonicalLineBundle.toPic = C.canonicalClass⁻¹ :=
  C.canonicalLineBundle.toPic_dual

/-- The chosen cotangent determinant has the recorded pure relative dimension. -/
theorem determinant_rank : C.cotangentDeterminant.rank = n :=
  C.cotangent_rank

/-- Two canonical-sheaf packages with isomorphic line representatives define the same class. -/
theorem canonicalClass_eq_of_iso {C' : CanonicalSheafData X n}
    (e : C.canonicalSheaf ≅ C'.canonicalSheaf) :
    C.canonicalClass = C'.canonicalClass :=
  C.canonicalLineBundle.toPic_eq_of_iso C'.canonicalLineBundle e

/-- An explicit Cartier representative of a canonical-sheaf package.

Existence is kept as data because the present Cartier-to-Picard API does not prove essential
surjectivity for every line bundle. -/
structure CanonicalDivisorData where
  /-- A Cartier divisor representing the canonical class. -/
  divisor : Scheme.CartierDivisor X.toVariety.toScheme
  /-- Its associated invertible sheaf is the canonical sheaf. -/
  associatedSheafIso :
    Scheme.CartierDivisor.associatedSheaf divisor ≅ C.canonicalSheaf

namespace CanonicalDivisorData

variable (D : CanonicalDivisorData C)

/-- The associated Cartier divisor maps to the canonical Picard class. -/
theorem toPic_eq_canonicalClass :
    Scheme.CartierDivisor.toPic D.divisor = C.canonicalClass := by
  apply Units.ext
  change Scheme.Modules.PicardClass.mk
      (Scheme.CartierDivisor.associatedSheaf D.divisor) =
    Scheme.Modules.PicardClass.mk C.canonicalSheaf
  exact (Scheme.Modules.PicardClass.mk_eq_mk_iff _ _).2 ⟨D.associatedSheafIso⟩

/-- The canonical Cartier divisor class. -/
noncomputable def canonicalDivisorClass :
    Scheme.CartierDivisor.ClassGroup X.toVariety.toScheme :=
  Scheme.CartierDivisor.toClass X.toVariety.toScheme D.divisor

/-- The Cartier class-to-Picard map sends the canonical divisor class to `[ω_X]`. -/
theorem classToPic_eq_canonicalClass :
    Scheme.CartierDivisor.classToPic
        (Multiplicative.ofAdd D.canonicalDivisorClass) = C.canonicalClass := by
  rw [canonicalDivisorClass, Scheme.CartierDivisor.classToPic_toClass]
  exact D.toPic_eq_canonicalClass

end CanonicalDivisorData

/-- Comparison data between a separately constructed dualizing-sheaf candidate and `ω_X`.

This structure deliberately contains no field claiming that `dualizingCandidate` is dualizing;
that property must come from a comparison with the constructed canonical complex. -/
structure DualizingSheafComparison
    (dualizingCandidate : X.toVariety.toScheme.Modules) where
  /-- On a smooth pure-dimensional target, the candidate is identified with `ω_X`. -/
  iso : dualizingCandidate ≅ C.canonicalSheaf

namespace DualizingSheafComparison

variable {C} {D : X.toVariety.toScheme.Modules}

/-- A dualizing-candidate comparison determines the candidate's Picard class whenever it is
equipped with line-bundle data. -/
theorem candidateClass_eq (E : DualizingSheafComparison C D)
    (L : Scheme.Modules.LineBundleData X.toVariety.toScheme)
    (hL : L.line ≅ D) :
    L.toPic = C.canonicalClass :=
  L.toPic_eq_of_iso C.canonicalLineBundle (hL ≪≫ E.iso)

end DualizingSheafComparison

end CanonicalSheafData

end SmoothProperVariety

end AlgebraicGeometry
