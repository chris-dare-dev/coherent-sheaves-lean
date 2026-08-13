/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.StabilityFunction.HarderNarasimhan

/-!
# Subobject lemmas for owner stability functions

These are the categorical primitives needed by the owner HN existence and
uniqueness arguments.  They are independent of the retained implementation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace BridgelandStabLean.Foundation

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace StabilityFunction

/-- A subobject has zero underlying object exactly when it is bottom. -/
@[simp]
theorem subobject_isZero_iff_eq_bot {E : A} (B : Subobject E) :
    IsZero (B : A) ↔ B = ⊥ := by
  constructor
  · intro hB
    have harrow : B.arrow = 0 := zero_of_source_iso_zero _ hB.isoZero
    rwa [← Subobject.mk_arrow B, Subobject.mk_eq_bot_iff_zero]
  · rintro rfl
    exact (isZero_zero A).of_iso Subobject.botCoeIsoZero

/-- A nonzero subobject is not bottom. -/
theorem subobject_ne_bot_of_not_isZero {E : A} {B : Subobject E}
    (hB : ¬IsZero (B : A)) : B ≠ ⊥ :=
  fun h => hB ((subobject_isZero_iff_eq_bot B).2 h)

/-- A subobject distinct from bottom has nonzero underlying object. -/
theorem subobject_not_isZero_of_ne_bot {E : A} {B : Subobject E}
    (hB : B ≠ ⊥) : ¬IsZero (B : A) :=
  fun h => hB ((subobject_isZero_iff_eq_bot B).1 h)

/-- The top and bottom subobjects of a nonzero object differ. -/
theorem subobject_top_ne_bot_of_not_isZero {E : A} (hE : ¬IsZero E) :
    (⊤ : Subobject E) ≠ ⊥ := by
  intro h
  apply hE
  have htop : IsZero ((⊤ : Subobject E) : A) :=
    (subobject_isZero_iff_eq_bot _).2 h
  exact htop.of_iso (asIso (⊤ : Subobject E).arrow).symm

/-- The inclusion from the bottom subobject is the zero morphism. -/
@[simp]
theorem subobject_ofLE_bot {E : A} (S : Subobject E) (h : ⊥ ≤ S) :
    Subobject.ofLE ⊥ S h = 0 :=
  zero_of_source_iso_zero _ Subobject.botCoeIsoZero

/-- The cokernel of the inclusion from bottom is the target subobject. -/
def subobjectCokernelBotIso {E : A} (S : Subobject E) (h : ⊥ ≤ S) :
    cokernel (Subobject.ofLE ⊥ S h) ≅ (S : A) := by
  rw [subobject_ofLE_bot S h]
  exact cokernelZeroIsoTarget

/-- A proper subobject of an abelian object has nonzero cokernel. -/
theorem cokernel_not_isZero_of_ne_top {E : A} {B : Subobject E}
    (hB : B ≠ ⊤) : ¬IsZero (cokernel B.arrow) := by
  intro hcoker
  haveI : Epi B.arrow := Preadditive.epi_of_isZero_cokernel B.arrow hcoker
  haveI : IsIso B.arrow := isIso_of_mono_of_epi B.arrow
  exact hB (Subobject.eq_top_of_isIso_arrow B)

end StabilityFunction

end BridgelandStabLean.Foundation
