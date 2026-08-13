/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.StabilityFunction.PhaseGeometry

/-!
# First uniqueness lemmas for owner HN filtrations

This file starts the owner-native uniqueness argument with its normalization
and semistable base cases.  Later leaves build the descent and tail-filtration
steps on this interface.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace BridgelandStabLean.Foundation

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace StabilityFunction

/-- Phase equality after propositionally rewriting both subobjects in a
successive quotient. -/
theorem phase_cokernel_ofLE_congr (Z : StabilityFunction A) {E : A}
    {A₁ A₂ B₁ B₂ : Subobject E} (hA : A₁ = A₂) (hB : B₁ = B₂)
    {h₁ : A₁ ≤ B₁} {h₂ : A₂ ≤ B₂} :
    Z.phase (cokernel (Subobject.ofLE A₁ B₁ h₁)) =
      Z.phase (cokernel (Subobject.ofLE A₂ B₂ h₂)) := by
  subst A₂
  subst B₂
  rfl

/-- Semistability is preserved after propositionally rewriting both
subobjects in a successive quotient. -/
theorem isSemistable_cokernel_ofLE_congr (Z : StabilityFunction A) {E : A}
    {A₁ A₂ B₁ B₂ : Subobject E} (hA : A₁ = A₂) (hB : B₁ = B₂)
    {h₁ : A₁ ≤ B₁} {h₂ : A₂ ≤ B₂}
    (hs : Z.IsSemistable (cokernel (Subobject.ofLE A₂ B₂ h₂))) :
    Z.IsSemistable (cokernel (Subobject.ofLE A₁ B₁ h₁)) := by
  subst A₂
  subst B₂
  exact hs

end StabilityFunction

namespace AbelianHNFiltration

/-- A semistable object can only have a one-factor HN filtration. -/
theorem n_eq_one_of_semistable {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (hE : Z.IsSemistable E) : F.n = 1 := by
  by_contra hn
  have hn_ge : 1 < F.n := by
    have := F.nonempty
    lia
  have hchain1_ne_bot : F.chain ⟨1, by lia⟩ ≠ ⊥ := by
    intro heq
    have h01 : F.chain ⟨0, by lia⟩ < F.chain ⟨1, by lia⟩ :=
      F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
    rw [F.chain_bot, heq] at h01
    exact lt_irrefl _ h01
  have hzero : F.chain (⟨0, F.nonempty⟩ : Fin F.n).castSucc = ⊥ := by
    change F.chain ⟨0, by lia⟩ = ⊥
    exact F.chain_bot
  have hfirst :
      Z.phase (F.chain ⟨1, by lia⟩ : A) = F.phase ⟨0, F.nonempty⟩ := by
    rw [← F.factor_phase ⟨0, F.nonempty⟩]
    exact ((Z.phase_cokernel_ofLE_congr hzero rfl).trans
      (Z.phase_eq_of_iso
        (StabilityFunction.subobjectCokernelBotIso
          (F.chain ⟨1, by lia⟩) bot_le))).symm
  have hfirst_le : F.phase ⟨0, F.nonempty⟩ ≤ Z.phase E := by
    rw [← hfirst]
    exact hE.2 _
      (StabilityFunction.subobject_not_isZero_of_ne_bot hchain1_ne_bot)
  let last : Fin F.n := ⟨F.n - 1, by lia⟩
  have hpenultimate_ne_top : F.chain ⟨F.n - 1, by lia⟩ ≠ ⊤ := by
    intro heq
    have hlt : F.chain ⟨F.n - 1, by lia⟩ < F.chain ⟨F.n, by lia⟩ :=
      F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
    rw [heq, F.chain_top] at hlt
    exact lt_irrefl _ hlt
  have hlast_top : F.chain last.succ = ⊤ := by
    have hindex : last.succ = ⟨F.n, by lia⟩ := Fin.ext (by simp [last]; lia)
    rw [hindex, F.chain_top]
  have hE_le_last : Z.phase E ≤ F.phase last := by
    have hquot := Z.phase_le_of_epi
      (cokernel.π (F.chain ⟨F.n - 1, by lia⟩).arrow) hE
      (StabilityFunction.cokernel_not_isZero_of_ne_top hpenultimate_ne_top)
    suffices Z.phase (cokernel (F.chain ⟨F.n - 1, by lia⟩).arrow) =
        F.phase last by linarith
    let S := F.chain ⟨F.n - 1, by lia⟩
    haveI : IsIso (⊤ : Subobject E).arrow := inferInstance
    calc
      Z.phase (cokernel S.arrow) =
          Z.phase (cokernel (Subobject.ofLE S ⊤ le_top)) :=
        Z.phase_eq_of_iso
          (cokernelIsoOfEq (Subobject.ofLE_arrow _).symm ≪≫
            cokernelCompIsIso _ _)
      _ = Z.phase (cokernel (Subobject.ofLE
          (F.chain last.castSucc) (F.chain last.succ)
          (le_of_lt (F.chain_strictMono last.castSucc_lt_succ)))) :=
        Z.phase_cokernel_ofLE_congr rfl hlast_top.symm
      _ = F.phase last := F.factor_phase last
  have hlast_lt : F.phase last < F.phase ⟨0, F.nonempty⟩ :=
    F.phase_strictAnti (Fin.mk_lt_mk.mpr (by lia))
  linarith

/-- A one-factor HN filtration identifies its ambient object as semistable. -/
theorem isSemistable_of_n_eq_one {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (hn : F.n = 1) : Z.IsSemistable E := by
  have hfactor := F.factor_semistable ⟨0, F.nonempty⟩
  have hzero : F.chain (⟨0, F.nonempty⟩ : Fin F.n).castSucc = ⊥ := by
    change F.chain ⟨0, by lia⟩ = ⊥
    exact F.chain_bot
  have htop : F.chain (⟨0, F.nonempty⟩ : Fin F.n).succ = ⊤ := by
    have hindex : (⟨0, F.nonempty⟩ : Fin F.n).succ = ⟨F.n, by lia⟩ :=
      Fin.ext (by simp; lia)
    rw [hindex, F.chain_top]
  have hnormalized :
      Z.IsSemistable (cokernel (Subobject.ofLE (⊥ : Subobject E) ⊤ bot_le)) :=
    Z.isSemistable_cokernel_ofLE_congr hzero.symm htop.symm hfactor
  exact Z.isSemistable_of_iso
    (StabilityFunction.subobjectCokernelBotIso ⊤ bot_le ≪≫
      asIso (⊤ : Subobject E).arrow)
    hnormalized

/-- A one-factor HN filtration is equivalent to semistability of its ambient
object. -/
theorem n_eq_one_iff_isSemistable {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) : F.n = 1 ↔ Z.IsSemistable E :=
  ⟨F.isSemistable_of_n_eq_one, F.n_eq_one_of_semistable⟩

/-- A non-semistable object has at least two HN factors. -/
theorem two_le_n_of_not_isSemistable {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (hE : ¬Z.IsSemistable E) : 2 ≤ F.n := by
  by_contra hlt
  apply hE
  apply F.isSemistable_of_n_eq_one
  have := F.nonempty
  lia

end AbelianHNFiltration

end BridgelandStabLean.Foundation
