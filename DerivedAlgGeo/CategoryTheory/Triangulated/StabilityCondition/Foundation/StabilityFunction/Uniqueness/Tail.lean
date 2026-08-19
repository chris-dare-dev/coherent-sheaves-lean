/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.StabilityFunction.Uniqueness.Extrema

/-!
# The tail filtration and uniqueness of length

This file owns the induction step: removing the first factor of a nontrivial HN
filtration and pushing the remaining chain to the quotient by its first nonzero
term, together with the length bookkeeping that makes the number of factors an
invariant of the object.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace AbelianHNFiltration

/-- Remove the first factor of a nontrivial HN filtration and push the
remaining chain to the quotient by its first nonzero term. -/
noncomputable def tail {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (hn : 2 ≤ F.n) :
    AbelianHNFiltration Z (cokernel (F.chain ⟨1, by lia⟩).arrow) where
  n := F.n - 1
  nonempty := by lia
  chain := fun ⟨j, _⟩ => imageSubobject
    ((F.chain ⟨j + 1, by lia⟩).arrow ≫
      cokernel.π (F.chain ⟨1, by lia⟩).arrow)
  chain_strictMono := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro ⟨j, hj⟩
    change imageSubobject ((F.chain ⟨j + 1, by lia⟩).arrow ≫
        cokernel.π (F.chain ⟨1, by lia⟩).arrow) <
      imageSubobject ((F.chain ⟨j + 2, by lia⟩).arrow ≫
        cokernel.π (F.chain ⟨1, by lia⟩).arrow)
    have hM₁ : F.chain ⟨1, by lia⟩ ≤ F.chain ⟨j + 1, by lia⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))
    have hM₂ : F.chain ⟨1, by lia⟩ ≤ F.chain ⟨j + 2, by lia⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))
    have hstep : F.chain ⟨j + 1, by lia⟩ < F.chain ⟨j + 2, by lia⟩ :=
      F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
    have hle : imageSubobject ((F.chain ⟨j + 1, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨1, by lia⟩).arrow) ≤
        imageSubobject ((F.chain ⟨j + 2, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨1, by lia⟩).arrow) := by
      rw [show (F.chain ⟨j + 1, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨1, by lia⟩).arrow =
        Subobject.ofLE _ _ hstep.le ≫
          ((F.chain ⟨j + 2, by lia⟩).arrow ≫
            cokernel.π (F.chain ⟨1, by lia⟩).arrow) by
        rw [← Category.assoc, Subobject.ofLE_arrow]]
      exact imageSubobject_comp_le _ _
    exact lt_of_le_of_ne hle (fun heq => (ne_of_lt hstep) <|
      (pullback_imageSubobject_eq Z hM₁).symm.trans
        (heq ▸ pullback_imageSubobject_eq Z hM₂))
  chain_bot := by
    change imageSubobject ((F.chain ⟨1, by lia⟩).arrow ≫
      cokernel.π (F.chain ⟨1, by lia⟩).arrow) = ⊥
    rw [cokernel.condition, imageSubobject_zero]
  chain_top := by
    change imageSubobject ((F.chain ⟨F.n - 1 + 1, by lia⟩).arrow ≫
      cokernel.π (F.chain ⟨1, by lia⟩).arrow) = ⊤
    have htop : F.chain ⟨F.n - 1 + 1, by lia⟩ = ⊤ :=
      (congrArg F.chain (Fin.ext (Nat.sub_add_cancel (by lia)))).trans F.chain_top
    rw [htop]
    haveI : IsIso (⊤ : Subobject E).arrow := inferInstance
    rw [imageSubobject_iso_comp]
    exact StabilityFunction.imageSubobject_eq_top_of_epi _
  phase := fun ⟨j, _⟩ => F.phase ⟨j + 1, by lia⟩
  phase_strictAnti := by
    intro ⟨j₁, _⟩ ⟨j₂, _⟩ h
    exact F.phase_strictAnti (Fin.mk_lt_mk.mpr (by simpa using h))
  factor_phase := by
    intro ⟨j, hj⟩
    exact (phase_cokernel_pullback_eq Z (F.chain ⟨1, by lia⟩) _).symm.trans
      ((Z.phase_cokernel_ofLE_congr
        (pullback_imageSubobject_eq Z
          (F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))))
        (pullback_imageSubobject_eq Z
          (F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))))).trans
        (F.factor_phase ⟨j + 1, by lia⟩))
  factor_semistable := by
    intro ⟨j, hj⟩
    have hM₁ : F.chain ⟨1, by lia⟩ ≤ F.chain ⟨j + 1, by lia⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))
    have hM₂ : F.chain ⟨1, by lia⟩ ≤ F.chain ⟨j + 2, by lia⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by lia))
    have hstep : F.chain ⟨j + 1, by lia⟩ < F.chain ⟨j + 2, by lia⟩ :=
      F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
    have hle : imageSubobject ((F.chain ⟨j + 1, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨1, by lia⟩).arrow) ≤
        imageSubobject ((F.chain ⟨j + 2, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨1, by lia⟩).arrow) := by
      rw [show (F.chain ⟨j + 1, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨1, by lia⟩).arrow =
        Subobject.ofLE _ _ hstep.le ≫
          ((F.chain ⟨j + 2, by lia⟩).arrow ≫
            cokernel.π (F.chain ⟨1, by lia⟩).arrow) by
        rw [← Category.assoc, Subobject.ofLE_arrow]]
      exact imageSubobject_comp_le _ _
    have hstrict : imageSubobject ((F.chain ⟨j + 1, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨1, by lia⟩).arrow) <
        imageSubobject ((F.chain ⟨j + 2, by lia⟩).arrow ≫
          cokernel.π (F.chain ⟨1, by lia⟩).arrow) :=
      lt_of_le_of_ne hle (fun heq => (ne_of_lt hstep) <|
        (pullback_imageSubobject_eq Z hM₁).symm.trans
          (heq ▸ pullback_imageSubobject_eq Z hM₂))
    exact Z.isSemistable_of_iso
      (cokernelPullbackIso Z (F.chain ⟨1, by lia⟩) hstrict)
      (Z.isSemistable_cokernel_ofLE_congr
        (pullback_imageSubobject_eq Z hM₁)
        (pullback_imageSubobject_eq Z hM₂)
        (F.factor_semistable ⟨j + 1, by lia⟩))

@[simp]
theorem tail_n {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (hn : 2 ≤ F.n) :
    (F.tail hn).n = F.n - 1 :=
  rfl

/-- Transporting an owner HN filtration along equality of its ambient objects
preserves the number of factors. -/
theorem transport_n {Z : StabilityFunction A} {E₁ E₂ : A}
    (h : E₁ = E₂) (F : AbelianHNFiltration Z E₁) :
    (h ▸ F).n = F.n := by
  subst h
  rfl

/-- Owner HN filtrations have a unique length when every object has a finite
subobject lattice.  The proof recursively removes the intrinsic first HN term
and descends to its strictly smaller quotient subobject lattice. -/
theorem n_eq {Z : StabilityFunction A} {E : A} (hE : ¬IsZero E)
    (hFinite : ∀ X : A, Finite (Subobject X))
    (F G : AbelianHNFiltration Z E) : F.n = G.n := by
  suffices main : ∀ k : ℕ, ∀ X : A, ¬IsZero X →
      Nat.card (Subobject X) ≤ k →
      ∀ F₁ F₂ : AbelianHNFiltration Z X, F₁.n = F₂.n by
    exact main _ E hE le_rfl F G
  intro k
  induction k with
  | zero =>
      intro X hX hcard F₁ F₂
      haveI := hFinite X
      haveI := Fintype.ofFinite (Subobject X)
      have hpositive : 0 < Nat.card (Subobject X) := by
        rw [Nat.card_eq_fintype_card]
        haveI : Nonempty (Subobject X) := ⟨⊥⟩
        exact Fintype.card_pos
      lia
  | succ k ih =>
      intro X hX hcard F₁ F₂
      haveI := hFinite X
      by_cases hsemistable : Z.IsSemistable X
      · exact (F₁.n_eq_one_of_semistable hsemistable).trans
          (F₂.n_eq_one_of_semistable hsemistable).symm
      · have hn₁ : 2 ≤ F₁.n := F₁.two_le_n_of_not_isSemistable hsemistable
        have hn₂ : 2 ≤ F₂.n := F₂.two_le_n_of_not_isSemistable hsemistable
        let M := F₁.chain ⟨1, by lia⟩
        have hMnonzero : M ≠ ⊥ := F₁.chain_one_ne_bot
        have hMproper : M ≠ ⊤ := by
          intro htop
          have hlt : F₁.chain ⟨1, by lia⟩ < F₁.chain ⟨F₁.n, by lia⟩ :=
            F₁.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
          change F₁.chain ⟨1, by lia⟩ = ⊤ at htop
          rw [F₁.chain_top, htop] at hlt
          exact lt_irrefl _ hlt
        have hcardQuotient : Nat.card (Subobject (cokernel M.arrow)) <
            Nat.card (Subobject X) := card_subobject_cokernel_lt hMnonzero
        have hfirst : F₂.chain ⟨1, by lia⟩ = M :=
          (F₁.chain_one_eq F₂).symm
        have hquotient : cokernel (F₂.chain ⟨1, by lia⟩).arrow =
            cokernel M.arrow := congrArg (fun S => cokernel (Subobject.arrow S)) hfirst
        have htail : (F₁.tail hn₁).n = (hquotient ▸ F₂.tail hn₂).n :=
          ih (cokernel M.arrow)
            (StabilityFunction.cokernel_not_isZero_of_ne_top hMproper)
            (by lia) _ _
        rw [F₁.tail_n, transport_n, F₂.tail_n] at htail
        lia

end AbelianHNFiltration

end CategoryTheory.Triangulated
