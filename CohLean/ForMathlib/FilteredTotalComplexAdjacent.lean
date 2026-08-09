/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.ForMathlib.FilteredTotalComplex
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.TotalComplexShift

/-!
# Adjacent layers of a column-filtered total complex

For a cohomological bicomplex of abelian groups, two consecutive stupid column truncations form a
degreewise split short exact sequence. Their quotient is the newly added column. After totalizing,
the mapping cone of the inclusion is quasi-isomorphic to that column shifted by its horizontal
degree. This identifies the initial page of the column-filtration spectral sequence with vertical
column homology.
-/

namespace HomologicalComplex₂

open CategoryTheory Category Limits

universe w

variable (K : HomologicalComplex₂ AddCommGrpCat.{w}
  (ComplexShape.up ℤ) (ComplexShape.up ℤ))

noncomputable def truncatedBicomplex (p : ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  K.stupidTrunc (ComplexShape.embeddingUpIntGE p)

noncomputable def singleColumnBicomplex (p : ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (CochainComplex.singleFunctor (CochainComplex AddCommGrpCat.{w} ℤ) p).obj (K.X p)

noncomputable def singleColumnXIso (p i : ℤ) (hi : i = p) :
    (singleColumnBicomplex K p).X i ≅ K.X p := by
  subst i
  exact HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p (K.X p)

@[reassoc (attr := simp)]
lemma singleColumnXIso_hom_inv_f (p i j : ℤ) (hi hi' : i = p) :
    (singleColumnXIso K p i hi).hom.f j ≫
      (singleColumnXIso K p i hi').inv.f j = 𝟙 _ := by
  subst i
  simp [singleColumnXIso, ← HomologicalComplex.comp_f]

@[reassoc (attr := simp)]
lemma singleColumnXIso_inv_hom_f (p i j : ℤ) (hi hi' : i = p) :
    (singleColumnXIso K p i hi).inv.f j ≫
      (singleColumnXIso K p i hi').hom.f j = 𝟙 _ := by
  subst i
  simp [singleColumnXIso, ← HomologicalComplex.comp_f]

noncomputable def adjacentColumnInclusion (p : ℤ) :
    truncatedBicomplex K (p + 1) ⟶ truncatedBicomplex K p :=
  HomologicalComplex.stupidTruncGEMap K p (p + 1) (by omega)

noncomputable def adjacentColumnProjection (p : ℤ) :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE p) ⟶ singleColumnBicomplex K p where
  f i := if hi : i = p then
      (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p)
        (i := 0) (by subst i; simp [ComplexShape.embeddingUpIntGE])).hom ≫
          (K.XIsoOfEq hi).hom ≫
          (singleColumnXIso K p i hi).inv
    else 0
  comm' i j hij := by
    by_cases hj : j = p
    · have hip : i < p := by
        dsimp [ComplexShape.up] at hij
        omega
      subst j
      apply IsZero.eq_of_src
      apply HomologicalComplex.isZero_stupidTrunc_X
      rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
      omega
    · rw [dif_neg hj]
      simp [singleColumnBicomplex]
      symm
      apply comp_zero

noncomputable def adjacentColumnBicomplexShortComplex (p : ℤ) :
    ShortComplex (HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :=
  ShortComplex.mk
    (adjacentColumnInclusion K p)
    (adjacentColumnProjection K p) (by
      apply HomologicalComplex.Hom.ext
      funext i
      rw [HomologicalComplex.comp_f]
      by_cases hi : p + 1 ≤ i
      · have hip : i ≠ p := by omega
        dsimp [adjacentColumnProjection]
        rw [dif_neg hip]
        apply comp_zero
      · apply IsZero.eq_of_src
        apply HomologicalComplex.isZero_stupidTrunc_X
        rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
        omega)

noncomputable instance totalFunctor_additive :
    (totalFunctor AddCommGrpCat.{w} (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).Additive where
  map_add := by
    intro X Y f g
    apply HomologicalComplex.Hom.ext
    funext n
    apply total.hom_ext
    intro i j h
    dsimp [totalFunctor]
    rw [ιTotal_map, HomologicalComplex.add_f_apply,
      HomologicalComplex.add_f_apply, Preadditive.add_comp,
      ← ιTotal_map X Y f, ← ιTotal_map X Y g]
    exact (Preadditive.comp_add _ _ _ _ _ _).symm

noncomputable def adjacentColumnTotalShortComplex (p : ℤ) :
    ShortComplex (CochainComplex AddCommGrpCat.{w} ℤ) :=
  (adjacentColumnBicomplexShortComplex K p).map
    (totalFunctor AddCommGrpCat.{w} (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ))

noncomputable def stupidTruncGEXIso (p i : ℤ) (hi : p ≤ i) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)).X i ≅ K.X i :=
  K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p)
    (i := (i - p).toNat) (by
      dsimp [ComplexShape.embeddingUpIntGE]
      rw [Int.toNat_of_nonneg (by omega)]
      omega)

@[simp]
lemma stupidTruncXIso_eq_stupidTruncGEXIso (p i : ℤ) (k : ℕ)
    (h : (ComplexShape.embeddingUpIntGE p).f k = i) :
    K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p) h =
      stupidTruncGEXIso K p i (by
        dsimp [ComplexShape.embeddingUpIntGE] at h
        omega) := by
  have hk : k = (i - p).toNat := by
    dsimp [ComplexShape.embeddingUpIntGE] at h
    rw [show i - p = (k : ℤ) by omega]
    simp
  subst k
  rfl

@[reassoc (attr := simp)]
lemma stupidTruncGEXIso_inv_hom_f (p i j : ℤ) (hi hi' : p ≤ i) :
    (stupidTruncGEXIso K p i hi).inv.f j ≫
      (stupidTruncGEXIso K p i hi').hom.f j = 𝟙 _ := by
  have : hi = hi' := Subsingleton.elim _ _
  subst this
  rw [← HomologicalComplex.comp_f,
    (stupidTruncGEXIso K p i hi).inv_hom_id,
    HomologicalComplex.id_f]

@[reassoc (attr := simp)]
lemma stupidTruncGEXIso_hom_inv_f (p i j : ℤ) (hi hi' : p ≤ i) :
    (stupidTruncGEXIso K p i hi).hom.f j ≫
      (stupidTruncGEXIso K p i hi').inv.f j = 𝟙 _ := by
  have : hi = hi' := Subsingleton.elim _ _
  subst this
  rw [← HomologicalComplex.comp_f,
    (stupidTruncGEXIso K p i hi).hom_inv_id,
    HomologicalComplex.id_f]

@[reassoc (attr := simp)]
lemma complexIso_inv_hom_f {A B : CochainComplex AddCommGrpCat.{w} ℤ}
    (e : A ≅ B) (j : ℤ) : e.inv.f j ≫ e.hom.f j = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, e.inv_hom_id, HomologicalComplex.id_f]

@[reassoc (attr := simp)]
lemma complexIso_hom_inv_f {A B : CochainComplex AddCommGrpCat.{w} ℤ}
    (e : A ≅ B) (j : ℤ) : e.hom.f j ≫ e.inv.f j = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, e.hom_inv_id, HomologicalComplex.id_f]

noncomputable def adjacentColumnTotalRetraction (p n : ℤ) :
    ((truncatedBicomplex K p).total
      (ComplexShape.up ℤ)).X n ⟶
    ((truncatedBicomplex K (p + 1)).total
      (ComplexShape.up ℤ)).X n :=
  HomologicalComplex₂.totalDesc _ (fun i j hij ↦
    if hi : p + 1 ≤ i then
      ((stupidTruncGEXIso K p i (by omega)).hom.f j ≫
        (stupidTruncGEXIso K (p + 1) i hi).inv.f j) ≫
        (truncatedBicomplex K (p + 1)).ιTotal
          (ComplexShape.up ℤ) i j n hij
    else 0)

noncomputable def adjacentColumnTotalSection (p n : ℤ) :
    ((singleColumnBicomplex K p).total (ComplexShape.up ℤ)).X n ⟶
    ((truncatedBicomplex K p).total
      (ComplexShape.up ℤ)).X n :=
  HomologicalComplex₂.totalDesc _ (fun i j hij ↦
    if hi : i = p then
      (((singleColumnXIso K p i hi).hom.f j ≫
        (K.XIsoOfEq hi).inv.f j) ≫
        (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p)
          (i := 0) (by subst i; simp [ComplexShape.embeddingUpIntGE])).inv.f j) ≫
        (truncatedBicomplex K p).ιTotal
          (ComplexShape.up ℤ) i j n hij
    else 0)

noncomputable def adjacentColumnTotalDegreewiseSplitting (p n : ℤ) :
    (((adjacentColumnTotalShortComplex K p).map
      (HomologicalComplex.eval AddCommGrpCat.{w} (ComplexShape.up ℤ) n)).Splitting) where
  r := adjacentColumnTotalRetraction K p n
  s := adjacentColumnTotalSection K p n
  f_r := by
    dsimp [adjacentColumnTotalShortComplex,
      adjacentColumnBicomplexShortComplex, totalFunctor]
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    by_cases hi : p + 1 ≤ i
    · rw [← Category.assoc, HomologicalComplex₂.ιTotal_map]
      dsimp [adjacentColumnTotalRetraction, truncatedBicomplex]
      rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
      simp only [dif_pos hi]
      simp [adjacentColumnInclusion,
        HomologicalComplex.stupidTruncGEMap, Category.assoc]
      rw [dif_pos hi]
      simp [HomologicalComplex.comp_f, Category.assoc]
    · apply IsZero.eq_of_src
      apply (HomologicalComplex.eval AddCommGrpCat.{w} (ComplexShape.up ℤ) j).map_isZero
      apply HomologicalComplex.isZero_stupidTrunc_X
      rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
      omega
  s_g := by
    dsimp [adjacentColumnTotalShortComplex,
      adjacentColumnBicomplexShortComplex, totalFunctor]
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    by_cases hi : i = p
    · rw [← Category.assoc]
      dsimp [adjacentColumnTotalSection, truncatedBicomplex]
      rw [HomologicalComplex₂.ι_totalDesc]
      simp only [dif_pos hi]
      rw [Category.assoc, Category.assoc, Category.assoc,
        HomologicalComplex₂.ιTotal_map]
      subst i
      simp [adjacentColumnProjection,
        singleColumnBicomplex,
        Category.assoc]
    · apply IsZero.eq_of_src
      apply (HomologicalComplex.eval AddCommGrpCat.{w} (ComplexShape.up ℤ) j).map_isZero
      apply HomologicalComplex.isZero_single_obj_X
      exact hi
  id := by
    dsimp [adjacentColumnTotalShortComplex,
      adjacentColumnBicomplexShortComplex, totalFunctor]
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    change (truncatedBicomplex K p).ιTotal (ComplexShape.up ℤ)
        i j n hij ≫ (_ + _) =
      (truncatedBicomplex K p).ιTotal (ComplexShape.up ℤ)
        i j n hij ≫ 𝟙 _
    by_cases hpi : p < i
    · have hi : p + 1 ≤ i := by omega
      have hip : i ≠ p := by omega
      rw [show (truncatedBicomplex K p).ιTotal (ComplexShape.up ℤ)
          i j n hij ≫ (_ + _) = _ + _ by
        apply Preadditive.comp_add]
      dsimp [adjacentColumnTotalRetraction,
        adjacentColumnTotalSection]
      rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
      simp only [dif_pos hi]
      rw [Category.assoc]
      erw [HomologicalComplex₂.ιTotal_map
        (truncatedBicomplex K (p + 1)) (truncatedBicomplex K p)
        (adjacentColumnInclusion K p) (ComplexShape.up ℤ) i j n hij]
      simp [adjacentColumnInclusion, HomologicalComplex.stupidTruncGEMap,
        adjacentColumnProjection, hip, Category.assoc]
      rw [dif_pos hi]
      let e₀ := stupidTruncGEXIso K p i (by omega)
      let e₁ := stupidTruncGEXIso K (p + 1) i hi
      change e₀.hom.f j ≫ e₁.inv.f j ≫
        ((e₁.hom.f j ≫ e₀.inv.f j) ≫
          (truncatedBicomplex K p).ιTotal
            (ComplexShape.up ℤ) i j n hij) = _
      rw [show (e₁.hom.f j ≫ e₀.inv.f j) ≫
          (truncatedBicomplex K p).ιTotal
            (ComplexShape.up ℤ) i j n hij =
        e₁.hom.f j ≫ e₀.inv.f j ≫
          (truncatedBicomplex K p).ιTotal
            (ComplexShape.up ℤ) i j n hij by apply Category.assoc,
        stupidTruncGEXIso_inv_hom_f_assoc,
        stupidTruncGEXIso_hom_inv_f_assoc]
    · by_cases hip : i = p
      · subst i
        rw [show (truncatedBicomplex K p).ιTotal (ComplexShape.up ℤ)
            p j n hij ≫ (_ + _) = _ + _ by
          apply Preadditive.comp_add]
        dsimp [adjacentColumnTotalRetraction,
          adjacentColumnTotalSection]
        rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
        rw [dif_neg (show ¬ p + 1 ≤ p by omega)]
        have hz : (0 : ((truncatedBicomplex K p).X p).X j ⟶
            ((truncatedBicomplex K (p + 1)).total
              (ComplexShape.up ℤ)).X n) ≫
              (HomologicalComplex₂.total.map
                (adjacentColumnInclusion K p)
                (ComplexShape.up ℤ)).f n = 0 := zero_comp
        rw [show (0 ≫ _) + _ = _ by rw [hz, zero_add]]
        rw [← Category.assoc, HomologicalComplex₂.ιTotal_map]
        dsimp [adjacentColumnProjection]
        rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
        simp [singleColumnBicomplex, Category.assoc]
        let e₀ := stupidTruncGEXIso K p p le_rfl
        let e₁ := singleColumnXIso K p p rfl
        change (e₀.hom.f j ≫ e₁.inv.f j) ≫
          e₁.hom.f j ≫ e₀.inv.f j ≫
            (truncatedBicomplex K p).ιTotal
              (ComplexShape.up ℤ) p j n hij = _
        rw [show (e₀.hom.f j ≫ e₁.inv.f j) ≫
            (e₁.hom.f j ≫ e₀.inv.f j ≫
              (truncatedBicomplex K p).ιTotal
                (ComplexShape.up ℤ) p j n hij) =
          e₀.hom.f j ≫ e₁.inv.f j ≫
            e₁.hom.f j ≫ e₀.inv.f j ≫
              (truncatedBicomplex K p).ιTotal
                (ComplexShape.up ℤ) p j n hij by apply Category.assoc,
          singleColumnXIso_inv_hom_f_assoc,
          stupidTruncGEXIso_hom_inv_f_assoc]
      · apply IsZero.eq_of_src
        apply (HomologicalComplex.eval AddCommGrpCat.{w} (ComplexShape.up ℤ) j).map_isZero
        apply HomologicalComplex.isZero_stupidTrunc_X
        rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
        omega

end HomologicalComplex₂

namespace HomologicalComplex₂

open CategoryTheory Category Limits

universe w

variable (A : CochainComplex AddCommGrpCat.{w} ℤ)

noncomputable def singleZeroBicomplex :
    HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (CochainComplex.singleFunctor (CochainComplex AddCommGrpCat.{w} ℤ) 0).obj A

noncomputable def singleZeroXIso (i : ℤ) (hi : i = 0) :
    (singleZeroBicomplex A).X i ≅ A := by
  subst i
  exact HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A

noncomputable def singleZeroTotalXIso (n : ℤ) :
    ((singleZeroBicomplex A).total (ComplexShape.up ℤ)).X n ≅ A.X n where
  hom := HomologicalComplex₂.totalDesc _ (fun i j hij ↦
    if hi : i = 0 then
      (singleZeroXIso A i hi).hom.f j ≫
        (A.XIsoOfEq (by dsimp at hij; omega)).hom
    else 0)
  inv := (singleZeroXIso A 0 rfl).inv.f n ≫
    (singleZeroBicomplex A).ιTotal (ComplexShape.up ℤ) 0 n n (by simp)
  hom_inv_id := by
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    by_cases hi : i = 0
    · subst i
      have hj : j = n := by dsimp at hij; omega
      subst j
      dsimp
      rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
      simp [singleZeroXIso]
    · apply IsZero.eq_of_src
      apply (HomologicalComplex.eval AddCommGrpCat.{w} (ComplexShape.up ℤ) j).map_isZero
      apply HomologicalComplex.isZero_single_obj_X
      exact hi
  inv_hom_id := by
    dsimp
    rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
    simp [singleZeroXIso]

noncomputable def singleZeroTotalIso :
    (singleZeroBicomplex A).total (ComplexShape.up ℤ) ≅ A :=
  HomologicalComplex.Hom.isoOfComponents (singleZeroTotalXIso A) (by
    intro n m hnm
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    by_cases hi : i = 0
    · subst i
      have hj : j = n := by dsimp at hij; omega
      subst j
      dsimp [singleZeroTotalXIso]
      rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
      simp [singleZeroXIso]
      rw [← Category.assoc, HomologicalComplex₂.total_d]
      let ι := (singleZeroBicomplex A).ιTotal (ComplexShape.up ℤ)
        0 n n hij
      let d₁ := (singleZeroBicomplex A).D₁ (ComplexShape.up ℤ) n m
      let d₂ := (singleZeroBicomplex A).D₂ (ComplexShape.up ℤ) n m
      let φ : ((singleZeroBicomplex A).total (ComplexShape.up ℤ)).X m ⟶
          A.X m := (singleZeroBicomplex A).totalDesc (fun i j hij ↦
        if h : i = 0 then
          (singleZeroXIso A i h).hom.f j ≫
            (A.XIsoOfEq (by
              change i + j = m at hij
              omega)).hom
        else 0)
      change ((singleZeroBicomplex A).X 0).d n m ≫
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℤ) 0 A).hom.f m =
        (ι ≫ (d₁ + d₂)) ≫ φ
      have hcomp : ι ≫ (d₁ + d₂) = ι ≫ d₁ + ι ≫ d₂ :=
        Preadditive.comp_add _ _ _ _ _ _
      have hadd : (ι ≫ d₁ + ι ≫ d₂) ≫ φ =
          (ι ≫ d₁) ≫ φ + (ι ≫ d₂) ≫ φ :=
        Preadditive.add_comp _ _ _ _ _ _
      refine Eq.trans ?_ ((congrArg (fun x ↦ x ≫ φ) hcomp).trans hadd).symm
      have ha₁ : (ι ≫ d₁) ≫ φ = ι ≫ d₁ ≫ φ := Category.assoc _ _ _
      have ha₂ : (ι ≫ d₂) ≫ φ = ι ≫ d₂ ≫ φ := Category.assoc _ _ _
      rw [ha₁, ha₂]
      dsimp [ι, d₁, d₂, φ]
      rw [HomologicalComplex₂.ι_D₁_assoc,
        HomologicalComplex₂.ι_D₂_assoc]
      rw [(singleZeroBicomplex A).d₁_eq' (ComplexShape.up ℤ)
        (show (ComplexShape.up ℤ).Rel 0 1 by rfl) n m]
      rw [(singleZeroBicomplex A).d₂_eq (ComplexShape.up ℤ)
        0 hnm m (by simp)]
      simp [singleZeroBicomplex]
      let δ := ((singleZeroBicomplex A).X 0).d n m
      let ιm := (singleZeroBicomplex A).ιTotal (ComplexShape.up ℤ)
        0 m m (by simp)
      let e := HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℤ) 0 A
      change δ ≫ e.hom.f m =
        (((1 : ℤˣ) • (0 : ((singleZeroBicomplex A).X 0).X n ⟶
          ((singleZeroBicomplex A).total (ComplexShape.up ℤ)).X m)) ≫ φ) +
        (((1 : ℤˣ) • (δ ≫ ιm)) ≫ φ)
      have hzero : (1 : ℤˣ) •
          (0 : ((singleZeroBicomplex A).X 0).X n ⟶
            ((singleZeroBicomplex A).total (ComplexShape.up ℤ)).X m) = 0 :=
        one_smul _ _
      have hvertical : (1 : ℤˣ) • (δ ≫ ιm) = δ ≫ ιm := one_smul _ _
      have hright :
          (((1 : ℤˣ) • (0 : ((singleZeroBicomplex A).X 0).X n ⟶
            ((singleZeroBicomplex A).total (ComplexShape.up ℤ)).X m)) ≫ φ) +
            (((1 : ℤˣ) • (δ ≫ ιm)) ≫ φ) =
          (0 ≫ φ) + ((δ ≫ ιm) ≫ φ) :=
        congrArg₂ (fun x y ↦ x + y)
          (congrArg (fun x ↦ x ≫ φ) hzero)
          (congrArg (fun x ↦ x ≫ φ) hvertical)
      refine Eq.trans ?_ hright.symm
      have hz : (0 : ((singleZeroBicomplex A).X 0).X n ⟶
          ((singleZeroBicomplex A).total (ComplexShape.up ℤ)).X m) ≫ φ = 0 :=
        zero_comp
      rw [show (0 ≫ φ) + ((δ ≫ ιm) ≫ φ) =
          ((δ ≫ ιm) ≫ φ) by rw [hz, zero_add]]
      have hdesc : ιm ≫ φ = e.hom.f m := by
        dsimp [ιm, φ, e]
        rw [HomologicalComplex₂.ι_totalDesc]
        simp [singleZeroXIso]
      exact (congrArg (fun x ↦ δ ≫ x) hdesc.symm).trans
        (Category.assoc δ ιm φ).symm
    · apply IsZero.eq_of_src
      apply (HomologicalComplex.eval AddCommGrpCat.{w} (ComplexShape.up ℤ) j).map_isZero
      apply HomologicalComplex.isZero_single_obj_X
      exact hi)

noncomputable def singleColumnShiftIso
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    singleColumnBicomplex K p ≅
      (shiftFunctor₁ AddCommGrpCat.{w} (-p)).obj
        (singleZeroBicomplex (K.X p)) :=
  (((CochainComplex.singleFunctors
    (CochainComplex AddCommGrpCat.{w} ℤ)).shiftIso
      (-p) p 0 (by omega)).app (K.X p)).symm

noncomputable def singleColumnTotalIso
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    (singleColumnBicomplex K p).total (ComplexShape.up ℤ) ≅
      (K.X p)⟦-p⟧ :=
  HomologicalComplex₂.total.mapIso (singleColumnShiftIso K p)
      (ComplexShape.up ℤ) ≪≫
    (singleZeroBicomplex (K.X p)).totalShift₁Iso (-p) ≪≫
    (shiftFunctor (CochainComplex AddCommGrpCat.{w} ℤ) (-p)).mapIso
      (singleZeroTotalIso (K.X p))

noncomputable def adjacentColumnTotalShortExact
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    (adjacentColumnTotalShortComplex K p).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact
    (adjacentColumnTotalShortComplex K p) (fun n ↦
      let s := adjacentColumnTotalDegreewiseSplitting K p n
      { mono_f := s.mono_f
        epi_g := s.epi_g
        exact := s.exact })

noncomputable def adjacentColumnConeToShift
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    CochainComplex.mappingCone (adjacentColumnTotalShortComplex K p).f ⟶
      (K.X p)⟦-p⟧ :=
  CochainComplex.mappingCone.descShortComplex
      (adjacentColumnTotalShortComplex K p) ≫
    (singleColumnTotalIso K p).hom

noncomputable instance adjacentColumnConeToShift_quasiIso
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    QuasiIso (adjacentColumnConeToShift K p) := by
  letI : QuasiIso
      (CochainComplex.mappingCone.descShortComplex
        (adjacentColumnTotalShortComplex K p)) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex
      (adjacentColumnTotalShortExact K p)
  dsimp [adjacentColumnConeToShift]
  infer_instance

/-- The adjacent filtration layer that contributes column `p`: the mapping cone of the map from
filtration stage `-p - 1` to stage `-p`. -/
noncomputable def columnFilteredAdjacentLayerComplex
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    CochainComplex AddCommGrpCat.{w} ℤ :=
  CochainComplex.mappingCone
    ((columnFilteredTotalComplex K).map
      (homOfLE (show -p - 1 ≤ -p by omega)))

private lemma mappingConeTotalStupidTruncGEMap_eq_of_eq
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (b₀ b₁ p : ℤ) (h : b₀ ≤ b₁) (hb₀ : b₀ = p) (hb₁ : b₁ = p + 1) :
    CochainComplex.mappingCone
      (total.map (HomologicalComplex.stupidTruncGEMap K b₀ b₁ h)
        (ComplexShape.up ℤ)) =
      CochainComplex.mappingCone
        (total.map (HomologicalComplex.stupidTruncGEMap K p (p + 1) (by omega))
          (ComplexShape.up ℤ)) := by
  subst b₀
  subst b₁
  rfl

/-- The filtration's adjacent mapping cone is the canonical adjacent-column mapping cone. -/
lemma columnFilteredAdjacentLayerComplex_eq
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    columnFilteredAdjacentLayerComplex K p =
      CochainComplex.mappingCone (adjacentColumnTotalShortComplex K p).f := by
  simp [columnFilteredAdjacentLayerComplex,
    columnFilteredTotalComplex, columnFiltrationBicomplex,
    adjacentColumnTotalShortComplex, adjacentColumnBicomplexShortComplex,
    adjacentColumnInclusion, truncatedBicomplex]
  exact mappingConeTotalStupidTruncGEMap_eq_of_eq K
    (- -p) (-(-p - 1)) p (by omega) (by omega) (by omega)

/-- The adjacent column-filtration layer maps quasi-isomorphically to the newly added column,
shifted so that total degree `p + q` corresponds to vertical degree `q`. -/
noncomputable def columnFilteredAdjacentLayerConeToShift
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    columnFilteredAdjacentLayerComplex K p ⟶ (K.X p)⟦-p⟧ :=
  eqToHom (columnFilteredAdjacentLayerComplex_eq K p) ≫
    adjacentColumnConeToShift K p

noncomputable instance columnFilteredAdjacentLayerConeToShift_quasiIso
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    QuasiIso (columnFilteredAdjacentLayerConeToShift K p) := by
  dsimp [columnFilteredAdjacentLayerConeToShift]
  infer_instance

/-- Homology of an adjacent filtration layer, identified with homology of the shifted new
column. -/
noncomputable def columnFilteredAdjacentLayerHomologyIso
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p n : ℤ) :
    (columnFilteredAdjacentLayerComplex K p).homology n ≅
      ((K.X p)⟦-p⟧).homology n := by
  letI : QuasiIso (columnFilteredAdjacentLayerConeToShift K p) :=
    columnFilteredAdjacentLayerConeToShift_quasiIso K p
  letI : QuasiIsoAt (columnFilteredAdjacentLayerConeToShift K p) n :=
    QuasiIso.quasiIsoAt n
  exact isoOfQuasiIsoAt (columnFilteredAdjacentLayerConeToShift K p) n

end HomologicalComplex₂
