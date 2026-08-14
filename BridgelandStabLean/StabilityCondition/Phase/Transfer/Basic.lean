/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.StabilityCondition.Symmetry.Autoequivalence.Slicing.Transport
import BridgelandStabLean.Foundation

/-!
# Preimage transfer of slicings

For a functor `F : C ⥤ D` and a slicing `s` on `D`, the raw phase collection

`P_F(phi)(E) := s.P phi (F.obj E)`

is the common categorical core of both constructions in arXiv:2607.28411v1,
Definitions 3.1 and 3.6.  Remarks 3.2 and 3.7 explicitly warn that this raw
collection need not be a slicing, even when `F` is conservative.  Accordingly,
`Slicing.PreimageData` records precisely the two slicing axioms which do not
follow formally from functoriality and shift compatibility: Hom-vanishing and
HN existence.

This factorization is deliberately honest about the theorem boundary.  The
geometric inducing results (Propositions 3.3 and 3.8, via Appendix A) are
expected to construct `PreimageData`; bare adjunction and conservativity do not.
-/

noncomputable section

open BridgelandStabLean.Foundation
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v₁ u₁ v₂ u₂

namespace BridgelandStabLean.Foundation

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The raw inverse-image phase collection along a functor.

It is intentionally only an `ObjectProperty`, not a `Slicing`: conservativity
alone does not supply Hom-vanishing or HN filtrations. -/
def Slicing.preimagePhase (s : Slicing D) (F : C ⥤ D) (phi : ℝ) :
    ObjectProperty C := fun E => s.P phi (F.obj E)

/-- Source-facing name for Definition 3.1 of arXiv:2607.28411v1.  A geometric
pullback slicing is computed using the direct-image functor. -/
abbrev Slicing.pullbackPhaseCollection (s : Slicing D) (push : C ⥤ D) :=
  s.preimagePhase push

/-- Source-facing name for Definition 3.6 of arXiv:2607.28411v1.  A geometric
pushforward slicing is computed using the inverse-image functor. -/
abbrev Slicing.pushforwardPhaseCollection (s : Slicing D) (pull : C ⥤ D) :=
  s.preimagePhase pull

/-- The genuinely missing axioms for turning the raw inverse-image phase
collection into a slicing.

Closure under isomorphisms, zero membership, and the shift law follow from
`s` and `F.CommShift`.  The two fields here are exactly what remains. -/
structure Slicing.PreimageData (s : Slicing D) (F : C ⥤ D) : Prop where
  /-- Hom-vanishing for objects whose images lie in separated phase slices. -/
  hom_vanishing : ∀ (phi₁ phi₂ : ℝ) (A B : C), phi₂ < phi₁ →
    s.P phi₁ (F.obj A) → s.P phi₂ (F.obj B) → ∀ g : A ⟶ B, g = 0
  /-- HN filtrations in the source with factors detected by `F`. -/
  hn_exists : ∀ E : C, Nonempty (HNFiltration C (s.preimagePhase F) E)

/-- Construct the genuine inverse-image slicing once the two non-formal axioms
have been supplied. -/
@[nolint unusedArguments]
def Slicing.preimage (s : Slicing D) (F : C ⥤ D) [F.Additive]
    [F.CommShift ℤ] [F.IsTriangulated] (h : s.PreimageData F) : Slicing C where
  P := s.preimagePhase F
  closedUnderIso phi := ⟨by
    intro X Y e hE
    change s.P phi (F.obj Y)
    exact ObjectProperty.prop_of_iso _ (F.mapIso e) hE⟩
  zero_mem phi := s.zero_mem_of_isZero D phi _ (F.map_isZero (isZero_zero C))
  shift_iff phi E := by
    change s.P phi (F.obj E) ↔
      s.P (phi + 1) (F.obj ((shiftFunctor C (1 : ℤ)).obj E))
    rw [s.shift_iff phi (F.obj E)]
    exact ⟨fun hE => ObjectProperty.prop_of_iso _
      ((F.commShiftIso (1 : ℤ)).app E).symm hE,
      fun hE => ObjectProperty.prop_of_iso _
        ((F.commShiftIso (1 : ℤ)).app E) hE⟩
  hom_vanishing := h.hom_vanishing
  hn_exists := h.hn_exists

@[simp]
theorem Slicing.preimage_P (s : Slicing D) (F : C ⥤ D) [F.Additive]
    [F.CommShift ℤ] [F.IsTriangulated] (h : s.PreimageData F)
    (phi : ℝ) (E : C) :
    (s.preimage F h).P phi E ↔ s.P phi (F.obj E) := by
  rfl

/-- For a faithful functor, target Hom-vanishing supplies the Hom component of
`PreimageData`; only HN existence remains to be proved. -/
def Slicing.PreimageData.ofFaithful (s : Slicing D) (F : C ⥤ D)
    [F.Additive] [F.Faithful]
    (hn : ∀ E : C, Nonempty (HNFiltration C (s.preimagePhase F) E)) :
    s.PreimageData F where
  hom_vanishing phi₁ phi₂ A B hphi hA hB g := by
    apply F.map_injective
    simpa using s.hom_vanishing phi₁ phi₂ (F.obj A) (F.obj B)
      hphi hA hB (F.map g)
  hn_exists := hn

/-- The preimage lifting criterion is stable under a uniform translation of
all phases. -/
def Slicing.PreimageData.phaseShift {s : Slicing D} {F : C ⥤ D}
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (h : s.PreimageData F) (t : ℝ) :
    Slicing.PreimageData (s.phaseShift D t) F where
  hom_vanishing phi₁ phi₂ A B hphi hA hB g :=
    h.hom_vanishing (phi₁ + t) (phi₂ + t) A B (by linarith) hA hB g
  hn_exists E := by
    obtain ⟨Fil⟩ := h.hn_exists E
    change Nonempty (HNFiltration C
      (fun psi X => s.P (psi + t) (F.obj X)) E)
    exact ⟨@BridgelandStabLean.Foundation.HNFiltration.phaseShift C _ _ _ _ _ _
      (s.preimage F h) E Fil t⟩

/-- Source-facing genuine pullback name.  Its explicit `PreimageData` argument
is the formal reminder that conservativity alone is insufficient. -/
abbrev Slicing.pullback (s : Slicing D) (push : C ⥤ D) [push.Additive]
    [push.CommShift ℤ] [push.IsTriangulated] (h : s.PreimageData push) :
    Slicing C := s.preimage push h

/-- Source-facing genuine pushforward name. -/
abbrev Slicing.pushforward (s : Slicing D) (pull : C ⥤ D) [pull.Additive]
    [pull.CommShift ℤ] [pull.IsTriangulated] (h : s.PreimageData pull) :
    Slicing C := s.preimage pull h

end BridgelandStabLean.Foundation
