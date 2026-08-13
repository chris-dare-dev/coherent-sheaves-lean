/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.Slicing.PhaseBounds

/-!
# Operations on repository-owned HN filtrations

This module supplies the elementary filtration constructors and transports
needed by phase truncations.  It remains on the Mathlib-only side of the
ownership boundary.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v

namespace BridgelandStabLean.Foundation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The empty HN filtration of a zero object. -/
def HNFiltration.zero {P : ℝ → ObjectProperty C} (E : C) (hE : IsZero E) :
    HNFiltration C P E where
  n := 0
  chain := ComposableArrows.mk₀ E
  triangle := fun i => Fin.elim0 i
  triangle_dist := fun i => Fin.elim0 i
  triangle_obj₁ := fun i => Fin.elim0 i
  triangle_obj₂ := fun i => Fin.elim0 i
  base_isZero := by simpa [ComposableArrows.left] using hE
  top_iso := ⟨by simpa [ComposableArrows.right] using Iso.refl E⟩
  zero_isZero := fun _ => hE
  φ := fun i => Fin.elim0 i
  hφ := fun i => Fin.elim0 i
  semistable := fun i => Fin.elim0 i

/-- The one-factor HN filtration of a semistable object. -/
def HNFiltration.single {P : ℝ → ObjectProperty C} (S : C) (φ : ℝ)
    (hS : P φ S) : HNFiltration C P S where
  n := 1
  chain := ComposableArrows.mk₁ (0 : (0 : C) ⟶ S)
  triangle := fun _ => Triangle.mk (0 : (0 : C) ⟶ S) (𝟙 S) 0
  triangle_dist := fun _ => contractible_distinguished₁ S
  triangle_obj₁ := fun _ =>
    ⟨eqToIso (by simp [ComposableArrows.obj', ComposableArrows.mk₁_obj])⟩
  triangle_obj₂ := fun _ =>
    ⟨eqToIso (by simp [ComposableArrows.obj', ComposableArrows.mk₁_obj])⟩
  base_isZero := isZero_zero C
  top_iso := ⟨eqToIso (by simp [ComposableArrows.right, ComposableArrows.mk₁_obj])⟩
  zero_isZero := fun h => by omega
  φ := fun _ => φ
  hφ := fun _ _ h => by omega
  semistable := fun i => by
    have hi : i = ⟨0, by omega⟩ := Fin.ext (by omega)
    subst hi
    exact hS

/-- Keep the first `k` factors of an HN filtration. -/
def HNFiltration.prefix {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (k : ℕ) (hk : k ≤ F.n) (hk₀ : 0 < k) :
    HNFiltration C P (F.chain.obj ⟨k, by omega⟩) where
  n := k
  chain := ComposableArrows.mkOfObjOfMapSucc
    (fun i : Fin (k + 1) => F.chain.obj ⟨i, by omega⟩)
    (fun i : Fin k => F.chain.map' i (i + 1) (by omega) (by omega))
  triangle := fun i => F.triangle ⟨i, by omega⟩
  triangle_dist := fun i => F.triangle_dist ⟨i, by omega⟩
  triangle_obj₁ := fun i => F.triangle_obj₁ ⟨i, by omega⟩
  triangle_obj₂ := fun i => F.triangle_obj₂ ⟨i, by omega⟩
  base_isZero := F.base_isZero
  top_iso := ⟨Iso.refl _⟩
  zero_isZero := fun h => by omega
  φ := fun i => F.φ ⟨i, by omega⟩
  hφ := by
    intro i j hij
    exact F.hφ (Fin.mk_lt_mk.mpr hij)
  semistable := fun i => F.semistable ⟨i, by omega⟩

@[simp]
theorem HNFiltration.prefix_φ {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (k : ℕ) (hk : k ≤ F.n) (hk₀ : 0 < k)
    (i : Fin k) : (F.prefix C k hk hk₀).φ i = F.φ ⟨i, by omega⟩ := rfl

/-- Append one lower-phase semistable factor along a distinguished triangle. -/
def HNFiltration.appendFactor {P : ℝ → ObjectProperty C} {Y Z : C}
    (G : HNFiltration C P Y) (T : Triangle C) (hT : T ∈ distTriang C)
    (e₁ : T.obj₁ ≅ Y) (e₂ : T.obj₂ ≅ Z) (ψ : ℝ) (hψ : P ψ T.obj₃)
    (hψ_lt : ∀ i : Fin G.n, ψ < G.φ i) : HNFiltration C P Z := by
  let obj : Fin (G.n + 2) → C := fun i =>
    if h : i ≤ G.n then G.chain.obj ⟨i, by omega⟩ else Z
  let last : G.chain.obj (Fin.last G.n) ⟶ Z :=
    (Classical.choice G.top_iso).hom ≫ e₁.inv ≫ T.mor₁ ≫ e₂.hom
  have mapSucc : ∀ i : Fin (G.n + 1), obj (Fin.castSucc i) ⟶ obj (Fin.succ i) := by
    rintro ⟨i, hi⟩
    simp only [obj, Fin.castSucc_mk, Fin.succ_mk]
    by_cases h : i + 1 ≤ G.n
    · simp only [show i ≤ G.n by omega, h, dite_true]
      exact G.chain.map' i (i + 1) (by omega) (by omega)
    · simp only [show i ≤ G.n by omega, h, dite_true, dite_false]
      exact eqToHom (by congr 1; ext; simp [Fin.val_last]; omega) ≫ last
  exact
    { n := G.n + 1
      chain := ComposableArrows.mkOfObjOfMapSucc obj mapSucc
      triangle := fun i => if h : i < G.n then G.triangle ⟨i, h⟩ else T
      triangle_dist := fun i => by
        split_ifs with h
        · exact G.triangle_dist ⟨i, h⟩
        · exact hT
      triangle_obj₁ := fun i => by
        have chainObj : ∀ k (hk : k ≤ G.n),
            (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).obj ⟨k, by omega⟩ =
              G.chain.obj ⟨k, by omega⟩ := by
          intro k hk
          simp [ComposableArrows.mkOfObjOfMapSucc_obj, obj, hk]
        split_ifs with h
        · exact ⟨(Classical.choice (G.triangle_obj₁ ⟨i, h⟩)).trans
            (eqToIso (by simpa [ComposableArrows.obj'] using (chainObj i (by omega)).symm))⟩
        · have hi : i = G.n := by omega
          exact ⟨e₁.trans ((Classical.choice G.top_iso).symm.trans (eqToIso (by
            change G.chain.obj (Fin.last G.n) =
              (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).obj' i _
            simp only [ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj,
              obj, show i ≤ G.n by omega, dite_true]
            congr 1
            ext
            simp [Fin.val_last, hi])))⟩
      triangle_obj₂ := fun i => by
        have chainObj : ∀ k (hk : k ≤ G.n),
            (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).obj ⟨k, by omega⟩ =
              G.chain.obj ⟨k, by omega⟩ := by
          intro k hk
          simp [ComposableArrows.mkOfObjOfMapSucc_obj, obj, hk]
        split_ifs with h
        · exact ⟨(Classical.choice (G.triangle_obj₂ ⟨i, h⟩)).trans
            (eqToIso (by simpa [ComposableArrows.obj'] using
              (chainObj (i + 1) (by omega)).symm))⟩
        · exact ⟨e₂.trans (eqToIso (by
            simp only [ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj,
              obj, show ¬(i + 1 ≤ G.n) by omega, dite_false]))⟩
      base_isZero := by
        change IsZero ((ComposableArrows.mkOfObjOfMapSucc obj mapSucc).obj ⟨0, by omega⟩)
        simp only [ComposableArrows.mkOfObjOfMapSucc_obj, obj,
          show (0 : ℕ) ≤ G.n by omega, dite_true]
        exact G.base_isZero
      top_iso := ⟨by
        change (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).obj
            ⟨G.n + 1, by omega⟩ ≅ Z
        simp only [ComposableArrows.mkOfObjOfMapSucc_obj, obj,
          show ¬(G.n + 1 ≤ G.n) by omega, dite_false]
        exact Iso.refl Z⟩
      zero_isZero := fun h => by omega
      φ := fun i => if h : i < G.n then G.φ ⟨i, h⟩ else ψ
      hφ := by
        intro i j hij
        rcases i with ⟨a, ha⟩
        rcases j with ⟨b, hb⟩
        have hab : a < b := Fin.mk_lt_mk.mp hij
        change (if h : b < G.n then G.φ ⟨b, h⟩ else ψ) <
          (if h : a < G.n then G.φ ⟨a, h⟩ else ψ)
        by_cases hb' : b < G.n
        · have ha' : a < G.n := by omega
          simp only [hb', ha', dite_true]
          exact G.hφ (Fin.mk_lt_mk.mpr hab)
        · by_cases ha' : a < G.n
          · simp only [hb', ha', dite_true, dite_false]
            exact hψ_lt ⟨a, ha'⟩
          · omega
      semistable := fun i => by
        change P (if h : i < G.n then G.φ ⟨i, h⟩ else ψ)
          ((if h : i < G.n then G.triangle ⟨i, h⟩ else T).obj₃)
        split_ifs with h
        · exact G.semistable ⟨i, h⟩
        · exact hψ }

/-- Shift every stage and factor of an HN filtration. -/
def HNFiltration.shift (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (a : ℤ) : HNFiltration C s.P (E⟦a⟧) where
  n := F.n
  chain := F.chain ⋙ shiftFunctor C a
  triangle := fun i => (Triangle.shiftFunctor C a).obj (F.triangle i)
  triangle_dist := fun i => Triangle.shift_distinguished _ (F.triangle_dist i) a
  triangle_obj₁ := fun i =>
    ⟨(shiftFunctor C a).mapIso (Classical.choice (F.triangle_obj₁ i))⟩
  triangle_obj₂ := fun i =>
    ⟨(shiftFunctor C a).mapIso (Classical.choice (F.triangle_obj₂ i))⟩
  base_isZero := (shiftFunctor C a).map_isZero F.base_isZero
  top_iso := ⟨(shiftFunctor C a).mapIso (Classical.choice F.top_iso)⟩
  zero_isZero := fun h => (shiftFunctor C a).map_isZero (F.zero_isZero h)
  φ := fun i => F.φ i + a
  hφ := by
    intro i j hij
    simpa [add_comm] using add_lt_add_right (F.hφ hij) a
  semistable := fun i => (s.shift_int C (F.φ i) _ a).mp (F.semistable i)

@[simp]
theorem HNFiltration.shift_phiPlus (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (a : ℤ) (h : 0 < F.n) :
    (F.shift C s a).phiPlus C h = F.phiPlus C h + a := rfl

@[simp]
theorem HNFiltration.shift_phiMinus (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (a : ℤ) (h : 0 < F.n) :
    (F.shift C s a).phiMinus C h = F.phiMinus C h + a := rfl

/-! ### Transporting phase cuts by shifts -/

/-- Shifting an upper phase cut shifts its endpoint by the same integer. -/
theorem Slicing.leProp_shift (s : Slicing C) (t : ℝ) (X : C) (a : ℤ)
    (hX : s.leProp C t X) : s.leProp C (t + a) (X⟦a⟧) := by
  rcases hX with hX | ⟨F, hF, hle⟩
  · exact Or.inl ((shiftFunctor C a).map_isZero hX)
  · refine Or.inr ⟨F.shift C s a, hF, ?_⟩
    simpa using add_le_add_right hle (a : ℝ)

/-- Shifting a strict lower phase cut shifts its endpoint by the same integer. -/
theorem Slicing.gtProp_shift (s : Slicing C) (t : ℝ) (X : C) (a : ℤ)
    (hX : s.gtProp C t X) : s.gtProp C (t + a) (X⟦a⟧) := by
  rcases hX with hX | ⟨F, hF, hgt⟩
  · exact Or.inl ((shiftFunctor C a).map_isZero hX)
  · refine Or.inr ⟨F.shift C s a, hF, ?_⟩
    simpa using add_lt_add_right hgt (a : ℝ)

/-- Shifting a strict upper phase cut shifts its endpoint by the same integer. -/
theorem Slicing.ltProp_shift (s : Slicing C) (t : ℝ) (X : C) (a : ℤ)
    (hX : s.ltProp C t X) : s.ltProp C (t + a) (X⟦a⟧) := by
  rcases hX with hX | ⟨F, hF, hlt⟩
  · exact Or.inl ((shiftFunctor C a).map_isZero hX)
  · refine Or.inr ⟨F.shift C s a, hF, ?_⟩
    simpa using add_lt_add_right hlt (a : ℝ)

/-- Shifting a lower phase cut shifts its endpoint by the same integer. -/
theorem Slicing.geProp_shift (s : Slicing C) (t : ℝ) (X : C) (a : ℤ)
    (hX : s.geProp C t X) : s.geProp C (t + a) (X⟦a⟧) := by
  rcases hX with hX | ⟨F, hF, hge⟩
  · exact Or.inl ((shiftFunctor C a).map_isZero hX)
  · refine Or.inr ⟨F.shift C s a, hF, ?_⟩
    simpa using add_le_add_right hge (a : ℝ)

/-! ### Reading phase bounds from filtrations -/

theorem Slicing.leProp_of_hn (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (t : ℝ) (h : ∀ i, F.φ i ≤ t) (hn : 0 < F.n) :
    s.leProp C t E := Or.inr ⟨F, hn, h ⟨0, hn⟩⟩

theorem Slicing.gtProp_of_hn (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (t : ℝ) (h : ∀ i, t < F.φ i) (hn : 0 < F.n) :
    s.gtProp C t E := Or.inr ⟨F, hn, h ⟨F.n - 1, by omega⟩⟩

theorem Slicing.ltProp_of_hn (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (t : ℝ) (h : ∀ i, F.φ i < t) (hn : 0 < F.n) :
    s.ltProp C t E := Or.inr ⟨F, hn, h ⟨0, hn⟩⟩

theorem Slicing.geProp_of_hn (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (t : ℝ) (h : ∀ i, t ≤ F.φ i) (hn : 0 < F.n) :
    s.geProp C t E := Or.inr ⟨F, hn, h ⟨F.n - 1, by omega⟩⟩

/-- A semistable object lies below any weak upper phase bound. -/
theorem Slicing.leProp_of_semistable (s : Slicing C) {S : C} {φ t : ℝ}
    (hS : s.P φ S) (h : φ ≤ t) : s.leProp C t S :=
  s.leProp_of_hn C (HNFiltration.single C S φ hS) t
    (fun _ => by simpa [HNFiltration.single] using h) (by change 0 < 1; omega)

/-- A semistable object lies above any strict lower phase bound. -/
theorem Slicing.gtProp_of_semistable (s : Slicing C) {S : C} {φ t : ℝ}
    (hS : s.P φ S) (h : t < φ) : s.gtProp C t S :=
  s.gtProp_of_hn C (HNFiltration.single C S φ hS) t
    (fun _ => by simpa [HNFiltration.single] using h) (by change 0 < 1; omega)

end BridgelandStabLean.Foundation
