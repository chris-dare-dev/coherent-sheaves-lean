/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.Cohomology.InjectiveCechAcyclic
import CohLean.Cohomology.CechTotalComparison
import Mathlib.CategoryTheory.Sites.CoversTop.Basic

/-!
# Global sections and the injective Cech total complex

For a cover of the terminal object, the augmented Cech complex of a sheaf is exact in degree
zero.  Combined with positive Cech exactness for injective sheaves, this identifies the total
Cech complex of an injective resolution with the ordinary global-sections complex.
-/

universe a u

open CategoryTheory Category Limits Opposite TopologicalSpace

namespace CategoryTheory.Sheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{a} C] {J : GrothendieckTopology C}
  [HasFiniteProducts C] [HasSheafify J AddCommGrpCat.{a}] {index : Type a}

omit [HasFiniteProducts C] in
private lemma evalOp_map_π
    {D : Type*} [Category D] [HasProducts D]
    (F : Cᵒᵖ ⥤ D) {V W : Limits.FormalCoproduct C} (m : V ⟶ W)
    (q : V.I) :
    ((Limits.FormalCoproduct.evalOp C D).obj F).map m.op ≫
        Limits.Pi.π (fun q ↦ F.obj (op (V.obj q))) q =
      Limits.Pi.π (fun q ↦ F.obj (op (W.obj q))) (m.f q) ≫
        F.map (m.φ q).op := by
  rw [Limits.FormalCoproduct.evalOp_obj_map]
  change Limits.Pi.lift (fun i ↦
      Limits.Pi.π (fun j ↦ F.obj (op (W.obj j))) (m.f i) ≫
        F.map (m.φ i).op) ≫
      Limits.Pi.π (fun q ↦ F.obj (op (V.obj q))) q = _
  rw [Limits.Pi.lift_π]

/-- Restriction of a global section to the degree-zero term of a Cech complex. -/
noncomputable def globalSectionsToCechZero
    {T : C} (hT : IsTerminal T) (U : index → C)
    (G : Sheaf J AddCommGrpCat.{a}) :
    G.obj.obj (op T) ⟶ ((cechComplexFunctor U).obj G.obj).X 0 := by
  let V := Limits.FormalCoproduct.mk index U
  change G.obj.obj (op T) ⟶
    ∏ᶜ fun q : (V.cech.obj (op (SimplexCategory.mk 0))).I ↦
      G.obj.obj (op ((V.cech.obj (op (SimplexCategory.mk 0))).obj q))
  exact Limits.Pi.lift fun q ↦
    G.obj.map (hT.from ((V.cech.obj (op (SimplexCategory.mk 0))).obj q)).op

omit [HasSheafify J AddCommGrpCat.{a}] in
lemma globalSectionsToCechZero_comp_d
    {T : C} (hT : IsTerminal T) (U : index → C)
    (G : Sheaf J AddCommGrpCat.{a}) :
    globalSectionsToCechZero hT U G ≫
      ((cechComplexFunctor U).obj G.obj).d 0 1 = 0 := by
  let V := Limits.FormalCoproduct.mk index U
  let Z := (Limits.FormalCoproduct.cosimplicialObjectFunctor V.cech).obj G.obj
  let T₀ : (V.cech.obj (op (SimplexCategory.mk 0))).I → AddCommGrpCat.{a} := fun r ↦
    G.obj.obj (op ((V.cech.obj (op (SimplexCategory.mk 0))).obj r))
  let T₁ : (V.cech.obj (op (SimplexCategory.mk 1))).I → AddCommGrpCat.{a} := fun r ↦
    G.obj.obj (op ((V.cech.obj (op (SimplexCategory.mk 1))).obj r))
  change globalSectionsToCechZero hT U G ≫
    ((cechComplexFunctor U).obj G.obj).d 0 1 =
      (0 : G.obj.obj (op T) ⟶ ∏ᶜ T₁)
  apply Limits.Pi.hom_ext
  intro q
  rw [zero_comp]
  have hd : ((cechComplexFunctor U).obj G.obj).d 0 1 =
      ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • Z.δ i := by
    change AlgebraicTopology.AlternatingCofaceMapComplex.objD Z 0 = _
    rfl
  let m₀ := V.cech.map (SimplexCategory.δ (0 : Fin 2)).op
  let m₁ := V.cech.map (SimplexCategory.δ (1 : Fin 2)).op
  have hZ₀ : Z.δ (0 : Fin 2) ≫ Limits.Pi.π
      (fun r : ((Limits.FormalCoproduct.mk index U).cech.obj
        (op (SimplexCategory.mk 1))).I ↦
          G.obj.obj (op (((Limits.FormalCoproduct.mk index U).cech.obj
            (op (SimplexCategory.mk 1))).obj r))) q =
      Limits.Pi.π T₀ (m₀.f q) ≫ G.obj.map (m₀.φ q).op := by
    exact evalOp_map_π G.obj m₀ q
  have hZ₁ : Z.δ (1 : Fin 2) ≫ Limits.Pi.π
      (fun r : ((Limits.FormalCoproduct.mk index U).cech.obj
        (op (SimplexCategory.mk 1))).I ↦
          G.obj.obj (op (((Limits.FormalCoproduct.mk index U).cech.obj
            (op (SimplexCategory.mk 1))).obj r))) q =
      Limits.Pi.π T₀ (m₁.f q) ≫ G.obj.map (m₁.φ q).op := by
    exact evalOp_map_π G.obj m₁ q
  have hglobal (r : (V.cech.obj (op (SimplexCategory.mk 0))).I) :
      globalSectionsToCechZero hT U G ≫ Limits.Pi.π T₀ r =
        G.obj.map (hT.from ((V.cech.obj (op (SimplexCategory.mk 0))).obj r)).op := by
    dsimp [globalSectionsToCechZero, T₀]
    rw [Limits.Pi.lift_π]
  rw [hd, Fin.sum_univ_two]
  rw [show (-1 : ℤ) ^ ((0 : Fin 2) : ℕ) = 1 by norm_num,
    show (-1 : ℤ) ^ ((1 : Fin 2) : ℕ) = -1 by norm_num]
  simp only [one_smul, neg_smul, Preadditive.comp_add, Preadditive.comp_neg,
    Preadditive.add_comp, Preadditive.neg_comp, Category.assoc]
  erw [hZ₀, hZ₁]
  simp only [← Category.assoc]
  rw [hglobal (m₀.f q), hglobal (m₁.f q)]
  simp only [← G.obj.map_comp]
  have hop :
      (hT.from ((V.cech.obj (op (SimplexCategory.mk 0))).obj (m₀.f q))).op ≫
          (m₀.φ q).op =
        (hT.from ((V.cech.obj (op (SimplexCategory.mk 0))).obj (m₁.f q))).op ≫
          (m₁.φ q).op := by
    rw [← op_comp, ← op_comp]
    congr 1
    apply hT.hom_ext
  rw [hop, add_neg_cancel]

omit [HasSheafify J AddCommGrpCat.{a}] in
/-- The sheaf gluing axiom identifies global sections with degree-zero Cech cocycles. -/
lemma globalSectionsToCechZero_exact
    {T : C} (hT : IsTerminal T) (U : index → C) (hU : J.CoversTop U)
    (G : Sheaf J AddCommGrpCat.{a}) :
    (ShortComplex.mk (globalSectionsToCechZero hT U G)
      (((cechComplexFunctor U).obj G.obj).d 0 1)
      (globalSectionsToCechZero_comp_d hT U G)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  let F := G.obj ⋙ forget AddCommGrpCat.{a}
  have hF : Presheaf.IsSheaf J F :=
    Presheaf.isSheaf_comp_of_isSheaf J G.obj
      (forget AddCommGrpCat.{a}) G.2
  let V := Limits.FormalCoproduct.mk index U
  let Zc := (Limits.FormalCoproduct.cosimplicialObjectFunctor V.cech).obj G.obj
  let T₀ : (V.power (Fin 1)).I → AddCommGrpCat.{a} := fun r ↦
    G.obj.obj (op ((V.power (Fin 1)).obj r))
  let T₁ : (V.power (Fin 2)).I → AddCommGrpCat.{a} := fun r ↦
    G.obj.obj (op ((V.power (Fin 2)).obj r))
  let m₀ : V.power (Fin 2) ⟶ V.power (Fin 1) :=
    V.mapPower (fun _ : Fin 1 ↦ (1 : Fin 2))
  let m₁ : V.power (Fin 2) ⟶ V.power (Fin 1) :=
    V.mapPower (fun _ : Fin 1 ↦ (0 : Fin 2))
  have hm₀ : V.cech.map (SimplexCategory.δ (0 : Fin 2)).op = m₀ := by
    change V.mapPower (SimplexCategory.δ (0 : Fin 2)).toOrderHom.toFun = _
    congr 1
    funext k
    fin_cases k
    rfl
  have hm₁ : V.cech.map (SimplexCategory.δ (1 : Fin 2)).op = m₁ := by
    change V.mapPower (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun = _
    congr 1
    funext k
    fin_cases k
    rfl
  let xV := Limits.Concrete.productEquiv T₀ x
  have hcocycle (q : (V.power (Fin 2)).I) :
      (ConcreteCategory.hom (G.obj.map (m₀.φ q).op)) (xV (m₀.f q)) =
        (ConcreteCategory.hom (G.obj.map (m₁.φ q).op)) (xV (m₁.f q)) := by
    have hd : ((cechComplexFunctor U).obj G.obj).d 0 1 =
        ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • Zc.δ i := by
      change AlgebraicTopology.AlternatingCofaceMapComplex.objD Zc 0 = _
      rfl
    have hδ₀ : Zc.δ (0 : Fin 2) =
        ((Limits.FormalCoproduct.evalOp C AddCommGrpCat.{a}).obj G.obj).map m₀.op := by
      change ((Limits.FormalCoproduct.evalOp C AddCommGrpCat.{a}).obj G.obj).map
        (V.cech.map (SimplexCategory.δ (0 : Fin 2)).op).op = _
      rw [hm₀]
    have hδ₁ : Zc.δ (1 : Fin 2) =
        ((Limits.FormalCoproduct.evalOp C AddCommGrpCat.{a}).obj G.obj).map m₁.op := by
      change ((Limits.FormalCoproduct.evalOp C AddCommGrpCat.{a}).obj G.obj).map
        (V.cech.map (SimplexCategory.δ (1 : Fin 2)).op).op = _
      rw [hm₁]
    have hZ₀ : Zc.δ (0 : Fin 2) ≫ Limits.Pi.π T₁ q =
        Limits.Pi.π T₀ (m₀.f q) ≫ G.obj.map (m₀.φ q).op := by
      rw [hδ₀]
      exact evalOp_map_π G.obj m₀ q
    have hZ₁ : Zc.δ (1 : Fin 2) ≫ Limits.Pi.π T₁ q =
        Limits.Pi.π T₀ (m₁.f q) ≫ G.obj.map (m₁.φ q).op := by
      rw [hδ₁]
      exact evalOp_map_π G.obj m₁ q
    have hmor : ((cechComplexFunctor U).obj G.obj).d 0 1 ≫ Limits.Pi.π T₁ q =
        (Limits.Pi.π T₀ (m₀.f q) ≫ G.obj.map (m₀.φ q).op) -
          (Limits.Pi.π T₀ (m₁.f q) ≫ G.obj.map (m₁.φ q).op) := by
      rw [hd, Fin.sum_univ_two]
      rw [show (-1 : ℤ) ^ ((0 : Fin 2) : ℕ) = 1 by norm_num,
        show (-1 : ℤ) ^ ((1 : Fin 2) : ℕ) = -1 by norm_num]
      simp only [one_smul, neg_smul, Preadditive.add_comp, Preadditive.neg_comp]
      rw [hZ₀, hZ₁]
      rw [sub_eq_add_neg]
    have hxq := congrArg
      (fun y ↦ (ConcreteCategory.hom (Limits.Pi.π T₁ q)) y) hx
    rw [map_zero] at hxq
    erw [← ConcreteCategory.comp_apply] at hxq
    erw [hmor] at hxq
    rw [show xV (m₀.f q) =
        (ConcreteCategory.hom (Limits.Pi.π T₀ (m₀.f q))) x by
      exact Limits.Concrete.productEquiv_apply_apply T₀ x (m₀.f q),
      show xV (m₁.f q) =
        (ConcreteCategory.hom (Limits.Pi.π T₀ (m₁.f q))) x by
      exact Limits.Concrete.productEquiv_apply_apply T₀ x (m₁.f q)]
    change (G.obj.map (m₀.φ q).op).hom
        ((Limits.Pi.π T₀ (m₀.f q)).hom x) =
      (G.obj.map (m₁.φ q).op).hom
        ((Limits.Pi.π T₀ (m₁.f q)).hom x)
    exact sub_eq_zero.mp hxq
  let r (i : index) : Fin 1 → index := fun _ ↦ i
  let e (i : index) : (V.power (Fin 1)).obj (r i) ≅ U i :=
    Limits.productUniqueIso (fun _ : Fin 1 ↦ U i)
  let family : Presheaf.FamilyOfElementsOnObjects F U := fun i ↦
    F.map (e i).inv.op (xV (r i))
  have hfamily : family.IsCompatible := by
    intro Z i j f g
    let q : Fin 2 → index :=
      fun k ↦ Fin.cases i (fun _ ↦ j) k
    let l : Z ⟶ ∏ᶜ fun k : Fin 2 ↦ U (q k) :=
      Limits.Pi.lift fun k ↦ Fin.cases f (fun _ ↦ g) k
    have hpair :
        F.map (Limits.Pi.π (fun k : Fin 2 ↦ U (q k)) 0).op (family i) =
          F.map (Limits.Pi.π (fun k : Fin 2 ↦ U (q k)) 1).op (family j) := by
      have hc := (hcocycle q).symm
      dsimp [m₀, m₁, V, q, r] at hc
      dsimp [family, F]
      erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← G.obj.map_comp, ← G.obj.map_comp]
      convert hc using 1
      · rfl
      · dsimp [q, r, e]
        have hmor :
            (Limits.productUniqueIso (fun _ : Fin 1 ↦ U i)).inv.op ≫
                (Limits.Pi.π (fun k : Fin 2 ↦
                  U (Fin.cases i (fun _ ↦ j) k)) 0).op =
              (Limits.Pi.lift fun _ : Fin 1 ↦
                (show (∏ᶜ fun k : Fin 2 ↦ U (Fin.cases i (fun _ ↦ j) k)) ⟶ U i from
                  Limits.Pi.π (fun k : Fin 2 ↦
                    U (Fin.cases i (fun _ ↦ j) k)) 0)).op := by
          with_reducible_and_instances
            have hunder :
                Limits.Pi.π (fun k : Fin 2 ↦
                    U (Fin.cases i (fun _ ↦ j) k)) 0 ≫
                    (Limits.productUniqueIso (fun _ : Fin 1 ↦ U i)).inv =
                  Limits.Pi.lift fun _ : Fin 1 ↦
                    (show (∏ᶜ fun k : Fin 2 ↦ U (Fin.cases i (fun _ ↦ j) k)) ⟶ U i from
                      Limits.Pi.π (fun k : Fin 2 ↦
                        U (Fin.cases i (fun _ ↦ j) k)) 0) := by
              apply Limits.Pi.hom_ext
              intro k
              have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
              subst k
              rw [Category.assoc, Limits.productUniqueIso_inv_π, Limits.Pi.lift_π]
              all_goals simp only [eqToHom_refl]
              all_goals with_unfolding_all exact Category.comp_id _
            simpa only [op_comp] using congrArg Quiver.Hom.op hunder
        rw [hmor]
        congr 1
      · dsimp [q, r, e]
        have hmor :
            (Limits.productUniqueIso (fun _ : Fin 1 ↦ U j)).inv.op ≫
                (Limits.Pi.π (fun k : Fin 2 ↦
                  U (Fin.cases i (fun _ ↦ j) k)) 1).op =
              (Limits.Pi.lift fun _ : Fin 1 ↦
                (show (∏ᶜ fun k : Fin 2 ↦ U (Fin.cases i (fun _ ↦ j) k)) ⟶ U j from
                  Limits.Pi.π (fun k : Fin 2 ↦
                    U (Fin.cases i (fun _ ↦ j) k)) 1)).op := by
          with_reducible_and_instances
            have hunder :
                Limits.Pi.π (fun k : Fin 2 ↦
                    U (Fin.cases i (fun _ ↦ j) k)) 1 ≫
                    (Limits.productUniqueIso (fun _ : Fin 1 ↦ U j)).inv =
                  Limits.Pi.lift fun _ : Fin 1 ↦
                    (show (∏ᶜ fun k : Fin 2 ↦ U (Fin.cases i (fun _ ↦ j) k)) ⟶ U j from
                      Limits.Pi.π (fun k : Fin 2 ↦
                        U (Fin.cases i (fun _ ↦ j) k)) 1) := by
              apply Limits.Pi.hom_ext
              intro k
              have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
              subst k
              rw [Category.assoc, Limits.productUniqueIso_inv_π, Limits.Pi.lift_π]
              all_goals simp only [eqToHom_refl]
              all_goals with_unfolding_all exact Category.comp_id _
            simpa only [op_comp] using congrArg Quiver.Hom.op hunder
        rw [hmor]
        congr 1
    have hpull := congrArg (fun y ↦ F.map l.op y) hpair
    have hli : l ≫ Limits.Pi.π (fun k : Fin 2 ↦ U (q k)) 0 = f := by
      dsimp [l]
      rw [Limits.Pi.lift_π]
      rfl
    have hlj : l ≫ Limits.Pi.π (fun k : Fin 2 ↦ U (q k)) 1 = g := by
      dsimp [l]
      rw [Limits.Pi.lift_π]
      rfl
    have hpulli :
        F.map l.op (F.map (Limits.Pi.π (fun k : Fin 2 ↦ U (q k)) 0).op
          (family i)) = F.map f.op (family i) := by
      rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, hli]
      rfl
    have hpullj :
        F.map l.op (F.map (Limits.Pi.π (fun k : Fin 2 ↦ U (q k)) 1).op
          (family j)) = F.map g.op (family j) := by
      rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, hlj]
      rfl
    change F.map f.op (family i) = F.map g.op (family j)
    exact hpulli.symm.trans (hpull.trans hpullj)
  let s := hfamily.section_ hU hF
  refine ⟨s.1 (op T), ?_⟩
  apply (Limits.Concrete.productEquiv T₀).injective
  funext q
  obtain ⟨i, rfl⟩ : ∃ i, q = r i := by
    refine ⟨q 0, ?_⟩
    funext k
    fin_cases k
    rfl
  rw [Limits.Concrete.productEquiv_apply_apply]
  erw [← ConcreteCategory.comp_apply]
  have hglobal : globalSectionsToCechZero hT U G ≫ Limits.Pi.π T₀ (r i) =
      G.obj.map (hT.from ((V.power (Fin 1)).obj (r i))).op := by
    dsimp [globalSectionsToCechZero, T₀, V]
    rw [Limits.Pi.lift_π]
  rw [hglobal]
  change F.map (hT.from ((V.power (Fin 1)).obj (r i))).op
      (s.1 (op T)) = xV (r i)
  have hs : s.1 (op (U i)) = family i := hfamily.section_apply hU hF i
  have hnat : F.map (hT.from (U i)).op (s.1 (op T)) = s.1 (op (U i)) :=
    Functor.sections_property s (hT.from (U i)).op
  have hterminal : hT.from ((V.power (Fin 1)).obj (r i)) =
      (e i).hom ≫ hT.from (U i) := hT.hom_ext _ _
  rw [hterminal, op_comp, F.map_comp]
  rw [ConcreteCategory.comp_apply]
  rw [hnat, hs]
  dsimp [family]
  erw [← ConcreteCategory.comp_apply, ← F.map_comp]
  simp

omit [HasSheafify J AddCommGrpCat.{a}] in
/-- Restriction to a family covering the terminal object is a monomorphism on global
sections. -/
lemma globalSectionsToCechZero_mono
    {T : C} (hT : IsTerminal T) (U : index → C) (hU : J.CoversTop U)
    (G : Sheaf J AddCommGrpCat.{a}) :
    Mono (globalSectionsToCechZero hT U G) := by
  rw [AddCommGrpCat.mono_iff_injective]
  intro x y hxy
  let F := G.obj ⋙ forget AddCommGrpCat.{a}
  have hF : Presheaf.IsSheaf J F :=
    Presheaf.isSheaf_comp_of_isSheaf J G.obj
      (forget AddCommGrpCat.{a}) G.2
  let V := Limits.FormalCoproduct.mk index U
  let T₀ : (V.power (Fin 1)).I → AddCommGrpCat.{a} := fun r ↦
    G.obj.obj (op ((V.power (Fin 1)).obj r))
  let r (i : index) : Fin 1 → index := fun _ ↦ i
  let e (i : index) : (V.power (Fin 1)).obj (r i) ≅ U i :=
    Limits.productUniqueIso (fun _ : Fin 1 ↦ U i)
  have hcover (i : index) :
      F.map (hT.from (U i)).op x = F.map (hT.from (U i)).op y := by
    have hq := congrArg
      (fun z ↦ (ConcreteCategory.hom (Limits.Pi.π T₀ (r i))) z) hxy
    erw [← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply] at hq
    have hglobal : globalSectionsToCechZero hT U G ≫ Limits.Pi.π T₀ (r i) =
        G.obj.map (hT.from ((V.power (Fin 1)).obj (r i))).op := by
      dsimp [globalSectionsToCechZero, T₀, V]
      rw [Limits.Pi.lift_π]
    rw [hglobal] at hq
    have hq' := congrArg
      (fun z ↦ F.map (e i).inv.op z) hq
    change F.map (e i).inv.op
        (F.map (hT.from ((V.power (Fin 1)).obj (r i))).op x) =
      F.map (e i).inv.op
        (F.map (hT.from ((V.power (Fin 1)).obj (r i))).op y) at hq'
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply] at hq'
    rw [← F.map_comp] at hq'
    rw [← op_comp] at hq'
    have ht : (e i).inv ≫ hT.from ((V.power (Fin 1)).obj (r i)) =
        hT.from (U i) := hT.hom_ext _ _
    simpa only [ht] using hq'
  have hType := (isSheaf_iff_isSheaf_of_type J F).1 hF
  apply (hType.isSeparated _ (hU T)).ext
  intro Z f hf
  obtain ⟨i, ⟨g⟩⟩ := hf
  have hft : f = g ≫ hT.from (U i) := hT.hom_ext _ _
  rw [hft, op_comp, F.map_comp, ConcreteCategory.comp_apply, hcover]
  rw [ConcreteCategory.comp_apply]

/-- Restriction of global sections to the degree-zero term of the integer-extended Cech
complex. -/
noncomputable def globalSectionsToCechIntZero
    {T : C} (hT : IsTerminal T) (U : index → C)
    (G : Sheaf J AddCommGrpCat.{a}) :
    G.obj.obj (op T) ⟶ ((cechCochainFunctorInt U).obj G).X 0 := by
  let K := (cechComplexFunctor U).obj G.obj
  change G.obj.obj (op T) ⟶
    (K.extend ComplexShape.embeddingUpNat).X (ComplexShape.embeddingUpNat.f 0)
  exact globalSectionsToCechZero hT U G ≫
    (K.extendXIso ComplexShape.embeddingUpNat rfl).inv

omit [HasSheafify J AddCommGrpCat.{a}] in
@[reassoc]
lemma globalSectionsToCechZero_naturality
    {T : C} (hT : IsTerminal T) (U : index → C)
    {G H : Sheaf J AddCommGrpCat.{a}} (f : G ⟶ H) :
    f.hom.app (op T) ≫ globalSectionsToCechZero hT U H =
      globalSectionsToCechZero hT U G ≫
        ((cechComplexFunctor U).map f.hom).f 0 := by
  let V := Limits.FormalCoproduct.mk index U
  let W := V.cech.obj (op (SimplexCategory.mk 0))
  let TG : W.I → AddCommGrpCat.{a} := fun q ↦
    G.obj.obj (op (W.obj q))
  let TH : W.I → AddCommGrpCat.{a} := fun q ↦
    H.obj.obj (op (W.obj q))
  change f.hom.app (op T) ≫ globalSectionsToCechZero hT U H =
    globalSectionsToCechZero hT U G ≫
      ((cechComplexFunctor U).map f.hom).f 0
  apply Limits.Pi.hom_ext
  intro q
  have hmap : ((cechComplexFunctor U).map f.hom).f 0 ≫
      Limits.Pi.π TH q =
    Limits.Pi.π TG q ≫ f.hom.app (op (W.obj q)) := by
    dsimp [cechComplexFunctor,
      Limits.FormalCoproduct.cochainComplexFunctor,
      Limits.FormalCoproduct.cosimplicialObjectFunctor, TG, TH, W, V]
    rw [Limits.Pi.map_π]
  have hglobalG : globalSectionsToCechZero hT U G ≫ Limits.Pi.π TG q =
      G.obj.map (hT.from (W.obj q)).op := by
    dsimp [globalSectionsToCechZero, TG, W, V]
    rw [Limits.Pi.lift_π]
  have hglobalH : globalSectionsToCechZero hT U H ≫ Limits.Pi.π TH q =
      H.obj.map (hT.from (W.obj q)).op := by
    dsimp [globalSectionsToCechZero, TH, W, V]
    rw [Limits.Pi.lift_π]
  change (f.hom.app (op T) ≫ globalSectionsToCechZero hT U H) ≫
      Limits.Pi.π TH q =
    (globalSectionsToCechZero hT U G ≫
      ((cechComplexFunctor U).map f.hom).f 0) ≫ Limits.Pi.π TH q
  rw [Category.assoc, Category.assoc, hmap]
  rw [hglobalH]
  rw [← Category.assoc, hglobalG]
  exact (f.hom.naturality _).symm

omit [HasSheafify J AddCommGrpCat.{a}] in
@[reassoc]
lemma globalSectionsToCechIntZero_naturality
    {T : C} (hT : IsTerminal T) (U : index → C)
    {G H : Sheaf J AddCommGrpCat.{a}} (f : G ⟶ H) :
    f.hom.app (op T) ≫ globalSectionsToCechIntZero hT U H =
      globalSectionsToCechIntZero hT U G ≫
        ((cechCochainFunctorInt U).map f).f 0 := by
  let KG := (cechComplexFunctor U).obj G.obj
  let KH := (cechComplexFunctor U).obj H.obj
  let φ := (cechComplexFunctor U).map f.hom
  change f.hom.app (op T) ≫ globalSectionsToCechZero hT U H ≫
      (KH.extendXIso ComplexShape.embeddingUpNat rfl).inv =
    globalSectionsToCechZero hT U G ≫
      (KG.extendXIso ComplexShape.embeddingUpNat rfl).inv ≫
        (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat).f
          (ComplexShape.embeddingUpNat.f 0)
  rw [HomologicalComplex.extendMap_f φ ComplexShape.embeddingUpNat rfl]
  with_reducible_and_instances
    dsimp only [KG, KH]
    rw [Iso.inv_hom_id_assoc]
    rw [globalSectionsToCechZero_naturality_assoc]

omit [HasSheafify J AddCommGrpCat.{a}] in
lemma globalSectionsToCechIntZero_comp_d
    {T : C} (hT : IsTerminal T) (U : index → C)
    (G : Sheaf J AddCommGrpCat.{a}) :
    globalSectionsToCechIntZero hT U G ≫
      ((cechCochainFunctorInt U).obj G).d 0 1 = 0 := by
  let K := (cechComplexFunctor U).obj G.obj
  change globalSectionsToCechZero hT U G ≫
      (K.extendXIso ComplexShape.embeddingUpNat rfl).inv ≫
        (K.extend ComplexShape.embeddingUpNat).d
          (ComplexShape.embeddingUpNat.f 0)
          (ComplexShape.embeddingUpNat.f 1) = 0
  with_reducible_and_instances
    rw [K.extend_d_eq ComplexShape.embeddingUpNat
      (i := 0) (j := 1) rfl rfl]
    rw [Iso.inv_hom_id_assoc]
    rw [← Category.assoc, globalSectionsToCechZero_comp_d, zero_comp]

omit [HasSheafify J AddCommGrpCat.{a}] in
/-- The degree-zero augmentation of the integer-extended Cech complex is exact. -/
lemma globalSectionsToCechIntZero_exact
    {T : C} (hT : IsTerminal T) (U : index → C) (hU : J.CoversTop U)
    (G : Sheaf J AddCommGrpCat.{a}) :
    (ShortComplex.mk (globalSectionsToCechIntZero hT U G)
      (((cechCochainFunctorInt U).obj G).d 0 1)
      (globalSectionsToCechIntZero_comp_d hT U G)).Exact := by
  let K := (cechComplexFunctor U).obj G.obj
  let Sℤ := ShortComplex.mk (globalSectionsToCechIntZero hT U G)
    (((cechCochainFunctorInt U).obj G).d 0 1)
    (globalSectionsToCechIntZero_comp_d hT U G)
  let Sℕ := ShortComplex.mk (globalSectionsToCechZero hT U G)
    (K.d 0 1) (globalSectionsToCechZero_comp_d hT U G)
  let e₀ : (K.extend ComplexShape.embeddingUpNat).X 0 ≅ K.X 0 :=
    K.extendXIso ComplexShape.embeddingUpNat rfl
  let e₁ : (K.extend ComplexShape.embeddingUpNat).X 1 ≅ K.X 1 :=
    K.extendXIso ComplexShape.embeddingUpNat rfl
  let e : Sℤ ≅ Sℕ := ShortComplex.isoMk (Iso.refl _)
    e₀ e₁ (by
      dsimp [Sℤ, Sℕ, globalSectionsToCechIntZero]
      with_reducible_and_instances
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp])
    (by
      dsimp [Sℤ, Sℕ, cechCochainFunctorInt, K]
      with_reducible_and_instances
        change e₀.hom ≫ K.d 0 1 =
          (K.extend ComplexShape.embeddingUpNat).d 0 1 ≫ e₁.hom
        have hd : (K.extend ComplexShape.embeddingUpNat).d 0 1 =
            e₀.hom ≫ K.d 0 1 ≫ e₁.inv :=
          K.extend_d_eq ComplexShape.embeddingUpNat
            (i := 0) (j := 1) (i' := (0 : ℤ)) (j' := (1 : ℤ)) rfl rfl
        rw [hd]
        simp)
  exact ShortComplex.exact_of_iso e.symm
    (globalSectionsToCechZero_exact hT U hU G)

omit [HasSheafify J AddCommGrpCat.{a}] in
/-- The integer-extended degree-zero augmentation remains monic. -/
lemma globalSectionsToCechIntZero_mono
    {T : C} (hT : IsTerminal T) (U : index → C) (hU : J.CoversTop U)
    (G : Sheaf J AddCommGrpCat.{a}) :
    Mono (globalSectionsToCechIntZero hT U G) := by
  letI : Mono (globalSectionsToCechZero hT U G) :=
    globalSectionsToCechZero_mono hT U hU G
  dsimp [globalSectionsToCechIntZero]
  infer_instance

/-- The natural augmentation from global sections in degree zero to the integer-extended Cech
complex. -/
noncomputable def globalSectionsToCechComplexNat
    {T : C} (hT : IsTerminal T) (U : index → C) :
    sectionsAtFunctorUnlifted (J := J) T ⋙
        HomologicalComplex.single AddCommGrpCat.{a} (ComplexShape.up ℤ) 0 ⟶
      cechCochainFunctorInt (J := J) U where
  app G := HomologicalComplex.mkHomFromSingle
    (globalSectionsToCechIntZero hT U G) (fun k hk ↦ by
      have hk' : k = 1 := by simpa using hk.symm
      subst k
      simpa using globalSectionsToCechIntZero_comp_d hT U G)
  naturality G H f := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [Functor.comp_obj, Functor.comp_map,
      HomologicalComplex.comp_f, HomologicalComplex.mkHomFromSingle_f,
      HomologicalComplex.single_map_f_self, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [cancel_epi]
    exact globalSectionsToCechIntZero_naturality hT U f

omit [HasSheafify J AddCommGrpCat.{a}] in
private lemma isZero_cechCochainFunctorInt_X_of_neg'
    (U : index → C) (G : Sheaf J AddCommGrpCat.{a}) (n : ℤ) (hn : n < 0) :
    IsZero (((cechCochainFunctorInt U).obj G).X n) := by
  dsimp [cechCochainFunctorInt]
  apply HomologicalComplex.isZero_extend_X
  intro k hk
  dsimp [ComplexShape.embeddingUpNat] at hk
  omega

/-- On a topological space, the global-sections augmentation of the Cech complex of an
injective sheaf is a quasi-isomorphism for every cover of the top open. -/
lemma globalSectionsToCechComplex_quasiIso_of_injective
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    (A : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective A] :
    QuasiIso ((globalSectionsToCechComplexNat Limits.isTerminalTop U).app A) := by
  let f := (globalSectionsToCechComplexNat Limits.isTerminalTop U).app A
  rw [quasiIso_iff]
  intro n
  by_cases hn₀ : n = 0
  · subst n
    rw [quasiIsoAt_iff' f (-1) 0 1 (by simp) (by simp)]
    rw [ShortComplex.quasiIso_iff_of_zeros]
    · let S := ShortComplex.mk
        (globalSectionsToCechIntZero Limits.isTerminalTop U A)
        (((cechCochainFunctorInt U).obj A).d 0 1)
        (globalSectionsToCechIntZero_comp_d Limits.isTerminalTop U A)
      refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
        ⟨globalSectionsToCechIntZero_exact Limits.isTerminalTop U hU A,
          globalSectionsToCechIntZero_mono Limits.isTerminalTop U hU A⟩
      exact ShortComplex.isoMk
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.up ℤ) 0 ((sectionsAtFunctorUnlifted ⊤).obj A))
        (Iso.refl _) (Iso.refl _) (by
          dsimp [f, globalSectionsToCechComplexNat, S]
          rw [HomologicalComplex.mkHomFromSingle_f, Category.comp_id])
        (by simp)
    · rfl
    · rfl
    · apply IsZero.eq_of_src
      exact isZero_cechCochainFunctorInt_X_of_neg' U A (-1) (by omega)
  · rw [quasiIsoAt_iff_exactAt f n]
    · by_cases hn : n < 0
      · exact HomologicalComplex.ExactAt.of_isZero
          (isZero_cechCochainFunctorInt_X_of_neg' U A n hn)
      · have hnpos : 0 < n := by omega
        let m := n.toNat
        have hm : (m : ℤ) = n := by
          dsimp [m]
          rw [Int.toNat_of_nonneg (by omega)]
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero
          (by dsimp [m]; omega : m ≠ 0)
        rw [← hm, hk]
        let K := (cechComplexFunctor U).obj A.obj
        apply (K.extend_exactAt_iff ComplexShape.embeddingUpNat
          (j := k + 1) (j' := ((k + 1 : ℕ) : ℤ)) rfl).2
        exact cechComplex_exactAt_succ_of_injective U hU A k
    · exact HomologicalComplex.exactAt_single_obj
        (ComplexShape.up ℤ) 0 ((sectionsAtFunctorUnlifted ⊤).obj A) n hn₀

/-- A row of the flipped bicomplex concentrated in degree zero is the corresponding single
complex. -/
private noncomputable def flippedSingleZeroRowIso
    (A : CochainComplex AddCommGrpCat.{u} ℤ) (p : ℤ) :
    ((HomologicalComplex₂.singleZeroBicomplex A).flip.X p) ≅
      (HomologicalComplex.single AddCommGrpCat.{u}
        (ComplexShape.up ℤ) 0).obj (A.X p) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun q ↦ ?_) ?_
  · by_cases hq : q = 0
    · subst q
      exact (HomologicalComplex.eval AddCommGrpCat.{u}
        (ComplexShape.up ℤ) p).mapIso
          (HomologicalComplex₂.singleZeroXIso A 0 rfl) ≪≫
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.up ℤ) 0 (A.X p)).symm
    · exact ((HomologicalComplex.eval AddCommGrpCat.{u}
          (ComplexShape.up ℤ) p).map_isZero
            (HomologicalComplex.isZero_single_obj_X
              (ComplexShape.up ℤ) 0 A q hq)).isoZero ≪≫
        (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) 0 (A.X p) q hq).isoZero.symm
  · intro q r hqr
    simp [HomologicalComplex₂.singleZeroBicomplex]

@[reassoc]
private lemma flippedSingleZeroRowIso_naturality
    (A : CochainComplex AddCommGrpCat.{u} ℤ) {p q : ℤ} :
    ((HomologicalComplex₂.singleZeroBicomplex A).flip.d p q) ≫
        (flippedSingleZeroRowIso A q).hom =
      (flippedSingleZeroRowIso A p).hom ≫
        (HomologicalComplex.single AddCommGrpCat.{u}
          (ComplexShape.up ℤ) 0).map (A.d p q) := by
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : n = 0
  · subst n
    dsimp [flippedSingleZeroRowIso]
    rw [HomologicalComplex.single_map_f_self]
    simp only [Category.assoc]
    exact (HomologicalComplex₂.singleZeroXIso A 0 rfl).hom.comm p q |>.symm
  · apply IsZero.eq_of_src
    exact (HomologicalComplex.eval AddCommGrpCat.{u}
      (ComplexShape.up ℤ) p).map_isZero
        (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) 0 A n hn)

/-- Apply the degree-zero global-sections functor to an injective resolution, retaining the
Cech complex as the inner direction. -/
noncomputable def globalSectionsCechResolutionBicomplexSource
    {X : TopCat.{u}} {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) :
    HomologicalComplex₂ AddCommGrpCat.{u}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  HomologicalComplex₂.flip
    (HomologicalComplex₂.singleZeroBicomplex
      (injectiveResolutionSectionsComplexUnlifted (⊤ : Opens X) I))

/-- The bicomplex map from global sections in Cech degree zero to the full Cech resolution
bicomplex. -/
noncomputable def globalSectionsToCechResolutionBicomplexMap
    {X : TopCat.{u}} {I₀ : Type u} (U : I₀ → Opens X)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    globalSectionsCechResolutionBicomplexSource I ⟶
      cechResolutionBicomplexUnflipped U I where
  f p := (flippedSingleZeroRowIso
      (injectiveResolutionSectionsComplexUnlifted (⊤ : Opens X) I) p).hom ≫
    (globalSectionsToCechComplexNat Limits.isTerminalTop U).app
      (I.cochainComplex.X p)
  comm' p q hpq := by
    let AΓ := injectiveResolutionSectionsComplexUnlifted (⊤ : Opens X) I
    change (flippedSingleZeroRowIso AΓ p).hom ≫
        (globalSectionsToCechComplexNat Limits.isTerminalTop U).app
            (I.cochainComplex.X p) ≫
          (cechCochainFunctorInt U).map (I.cochainComplex.d p q) =
      ((HomologicalComplex₂.singleZeroBicomplex AΓ).flip.d p q) ≫
        (flippedSingleZeroRowIso AΓ q).hom ≫
          (globalSectionsToCechComplexNat Limits.isTerminalTop U).app
            (I.cochainComplex.X q)
    have hα := (globalSectionsToCechComplexNat Limits.isTerminalTop U).naturality
      (I.cochainComplex.d p q)
    change (HomologicalComplex.single AddCommGrpCat.{u}
        (ComplexShape.up ℤ) 0).map (AΓ.d p q) ≫
          (globalSectionsToCechComplexNat Limits.isTerminalTop U).app
            (I.cochainComplex.X q) =
      (globalSectionsToCechComplexNat Limits.isTerminalTop U).app
          (I.cochainComplex.X p) ≫
        (cechCochainFunctorInt U).map (I.cochainComplex.d p q) at hα
    rw [← hα]
    rw [flippedSingleZeroRowIso_naturality_assoc]

/-- The global-sections source bicomplex is connective in Cech degree. -/
lemma globalSectionsCechResolutionBicomplexSource_verticallyConnective
    {X : TopCat.{u}} {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) :
    HomologicalComplex₂.IsVerticallyConnective
      (globalSectionsCechResolutionBicomplexSource I) := by
  intro p q hq
  let A := injectiveResolutionSectionsComplexUnlifted (⊤ : Opens X) I
  change IsZero ((HomologicalComplex.eval AddCommGrpCat.{u}
    (ComplexShape.up ℤ) q).obj
      ((HomologicalComplex₂.singleZeroBicomplex A).flip.X p))
  exact IsZero.of_iso
      (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) 0 (A.X p) q (by omega))
      ((HomologicalComplex.eval AddCommGrpCat.{u}
        (ComplexShape.up ℤ) q).mapIso
          (flippedSingleZeroRowIso A p))

/-- The full Cech resolution bicomplex is connective in Cech degree. -/
lemma cechResolutionBicomplexUnflipped_verticallyConnective
    {X : TopCat.{u}} {I₀ : Type u} (U : I₀ → Opens X)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    HomologicalComplex₂.IsVerticallyConnective
      (cechResolutionBicomplexUnflipped U I) := by
  intro p q hq
  change IsZero (((cechCochainFunctorInt U).obj (I.cochainComplex.X p)).X q)
  exact isZero_cechCochainFunctorInt_X_of_neg' U _ q hq

/-- The global-sections source bicomplex is connective in resolution degree. -/
lemma globalSectionsCechResolutionBicomplexSource_horizontallyConnective
    {X : TopCat.{u}} {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) :
    HomologicalComplex₂.IsHorizontallyConnective
      (globalSectionsCechResolutionBicomplexSource I) := by
  intro p q hp
  let A := injectiveResolutionSectionsComplexUnlifted (⊤ : Opens X) I
  have hA : IsZero (A.X p) :=
    (sectionsAtFunctorUnlifted (⊤ : Opens X)).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 p hp)
  change IsZero ((HomologicalComplex.eval AddCommGrpCat.{u}
    (ComplexShape.up ℤ) q).obj
      ((HomologicalComplex₂.singleZeroBicomplex A).flip.X p))
  exact IsZero.of_iso
      ((HomologicalComplex.eval AddCommGrpCat.{u}
        (ComplexShape.up ℤ) q).map_isZero
          ((HomologicalComplex.single AddCommGrpCat.{u}
            (ComplexShape.up ℤ) 0).map_isZero hA))
      ((HomologicalComplex.eval AddCommGrpCat.{u}
        (ComplexShape.up ℤ) q).mapIso
          (flippedSingleZeroRowIso A p))

/-- The full Cech resolution bicomplex is connective in resolution degree. -/
lemma cechResolutionBicomplexUnflipped_horizontallyConnective
    {X : TopCat.{u}} {I₀ : Type u} (U : I₀ → Opens X)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    HomologicalComplex₂.IsHorizontallyConnective
      (cechResolutionBicomplexUnflipped U I) := by
  intro p q hp
  change IsZero (((cechCochainFunctorInt U).obj (I.cochainComplex.X p)).X q)
  exact (HomologicalComplex.eval AddCommGrpCat.{u}
    (ComplexShape.up ℤ) q).map_isZero
      ((cechCochainFunctorInt U).map_isZero
        (CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 p hp))

/-- The total global-sections-to-Cech map of an injective resolution is a quasi-isomorphism. -/
lemma globalSectionsToCechResolution_total_quasiIso
    {X : TopCat.{u}} {I₀ : Type u} (U : I₀ → Opens X)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    QuasiIso (HomologicalComplex₂.total.map
      (globalSectionsToCechResolutionBicomplexMap U I) (ComplexShape.up ℤ)) := by
  apply HomologicalComplex₂.totalMap_quasiIso
  · exact globalSectionsCechResolutionBicomplexSource_verticallyConnective I
  · exact cechResolutionBicomplexUnflipped_verticallyConnective U I
  · exact globalSectionsCechResolutionBicomplexSource_horizontallyConnective I
  · exact cechResolutionBicomplexUnflipped_horizontallyConnective U I
  · intro n
    letI : QuasiIso ((globalSectionsToCechComplexNat Limits.isTerminalTop U).app
        (I.cochainComplex.X (n : ℤ))) :=
      globalSectionsToCechComplex_quasiIso_of_injective
        U hU (I.cochainComplex.X (n : ℤ))
    dsimp [globalSectionsToCechResolutionBicomplexMap]
    infer_instance

/-- The total of the source bicomplex is canonically the ordinary global-sections complex of
the injective resolution. -/
noncomputable def globalSectionsCechResolutionBicomplexSourceTotalIso
    {X : TopCat.{u}} {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) :
    (globalSectionsCechResolutionBicomplexSource I).total (ComplexShape.up ℤ) ≅
      injectiveResolutionSectionsComplexUnlifted (⊤ : Opens X) I := by
  let A := injectiveResolutionSectionsComplexUnlifted (⊤ : Opens X) I
  exact (HomologicalComplex₂.singleZeroBicomplex A).totalFlipIso
      (ComplexShape.up ℤ) ≪≫
    HomologicalComplex₂.singleZeroTotalIso A

/-- The comparison from the ordinary global-sections complex of an injective resolution to
the total Cech complex of that resolution. -/
noncomputable def globalSectionsToInjectiveCechTotalMap
    {X : TopCat.{u}} {I₀ : Type u} (U : I₀ → Opens X)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    injectiveResolutionSectionsComplexUnlifted (⊤ : Opens X) I ⟶
      cechInjectiveTotalComplex U I :=
  (globalSectionsCechResolutionBicomplexSourceTotalIso I).inv ≫
    HomologicalComplex₂.total.map
      (globalSectionsToCechResolutionBicomplexMap U I) (ComplexShape.up ℤ) ≫
    ((cechResolutionBicomplexUnflipped U I).totalFlipIso
      (ComplexShape.up ℤ)).inv

/-- For a cover of the top open, the global-sections comparison with the injective Cech total
complex is a quasi-isomorphism. -/
lemma globalSectionsToInjectiveCechTotalMap_quasiIso
    {X : TopCat.{u}} {I₀ : Type u} (U : I₀ → Opens X)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    QuasiIso (globalSectionsToInjectiveCechTotalMap U I) := by
  letI : QuasiIso (HomologicalComplex₂.total.map
      (globalSectionsToCechResolutionBicomplexMap U I) (ComplexShape.up ℤ)) :=
    globalSectionsToCechResolution_total_quasiIso U hU I
  dsimp [globalSectionsToInjectiveCechTotalMap]
  infer_instance

/-- Degreewise homology comparison between global sections of an injective resolution and its
Cech total complex. -/
noncomputable def globalSectionsCohomologyIsoInjectiveCechTotalHomology
    {X : TopCat.{u}} {I₀ : Type u} (U : I₀ → Opens X)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℤ) :
    (injectiveResolutionSectionsComplexUnlifted (⊤ : Opens X) I).homology n ≅
      (cechInjectiveTotalComplex U I).homology n := by
  letI : QuasiIso (globalSectionsToInjectiveCechTotalMap U I) :=
    globalSectionsToInjectiveCechTotalMap_quasiIso U hU I
  exact isoOfQuasiIsoAt (globalSectionsToInjectiveCechTotalMap U I) n

/-- In one universe, lifting an additive commutative group is naturally isomorphic to leaving
it unchanged. -/
private noncomputable def addCommGrpUliftSelfNatIso :
  AddCommGrpCat.uliftFunctor.{u, u} ≅ 𝟭 AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun A ↦ AddEquiv.ulift.toAddCommGrpIso) (fun f ↦ by
    ext x
    rfl)

/-- The universe-lifted sections complex used by Mathlib's `Ext` model agrees with the
unlifted complex used by the Cech construction. -/
private noncomputable def injectiveResolutionSectionsComplexIsoUnlifted
    {X : TopCat.{u}} {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) :
    injectiveResolutionSectionsComplex (⊤ : Opens X) I ≅
      injectiveResolutionSectionsComplexUnlifted (⊤ : Opens X) I :=
  (NatIso.mapHomologicalComplex addCommGrpUliftSelfNatIso
    (ComplexShape.up ℤ)).app
      (injectiveResolutionSectionsComplexUnlifted (⊤ : Opens X) I)

/-- Cohomology of the ordinary global-sections complex of an injective resolution is derived
global sheaf cohomology. -/
noncomputable def injectiveResolutionGlobalSectionsCohomologyAddEquivH
    {X : TopCat.{u}} {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F)
    [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)] (n : ℕ) :
    (injectiveResolutionSectionsComplexUnlifted
      (⊤ : Opens X) I).homology (n : ℤ) ≃+
        @H (Opens X) _ (Opens.grothendieckTopology X) F _ hExt n :=
  ((HomologicalComplex.homologyMapIso
    (injectiveResolutionSectionsComplexIsoUnlifted I).symm
      (n : ℤ)).addCommGroupIsoToAddEquiv).trans
    ((@injectiveResolutionSectionsCohomologyAddEquivHPrime
      (Opens X) _ (Opens.grothendieckTopology X) _ hExt F
        (⊤ : Opens X) I n).trans
      (@HPrimeAddEquivH (Opens X) _ (Opens.grothendieckTopology X) _ hExt
        (⊤ : Opens X) Limits.isTerminalTop F n))

/-- The explicit comparison isomorphism from Cech cohomology to derived global sheaf
cohomology under the Leray acyclicity hypothesis. -/
noncomputable def cechCohomologyAddEquivDerived
    {X : TopCat.{u}} {I₀ : Type u} (U : I₀ → Opens X)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (hcover : @IsCechAcyclicCover (Opens X) _ (Opens.grothendieckTopology X)
      _ hExt I₀ _ U F) (n : ℕ) :
    (cechCohomology U F.obj n : AddCommGrpCat.{u}) ≃+
      @H (Opens X) _ (Opens.grothendieckTopology X) F _ hExt n :=
  ((((cechComplexFunctor U).obj F.obj).extendHomologyIso
      ComplexShape.embeddingUpNat rfl).symm ≪≫
    @cechCohomologyIsoInjectiveTotalHomology (Opens X) _
      (Opens.grothendieckTopology X) _ _ I₀ F U I hExt hcover.2 (n : ℤ) ≪≫
    (globalSectionsCohomologyIsoInjectiveCechTotalHomology
      U hcover.1 I (n : ℤ)).symm).addCommGroupIsoToAddEquiv.trans
        (injectiveResolutionGlobalSectionsCohomologyAddEquivH (hExt := hExt) I n)

/-- A Cech-acyclic cover of a topological space computes derived global sheaf cohomology in
every degree. -/
theorem cechComputesDerivedCohomology_of_isCechAcyclicCover
    {X : TopCat.{u}} {I₀ : Type u} (U : I₀ → Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (I : InjectiveResolution F)
    [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (hcover : @IsCechAcyclicCover (Opens X) _ (Opens.grothendieckTopology X)
      _ hExt I₀ _ U F) :
    @CechComputesDerivedCohomology (Opens X) _ (Opens.grothendieckTopology X)
      _ hExt I₀ _ U F := by
  intro n
  exact ⟨cechCohomologyAddEquivDerived (hExt := hExt) U I hcover n⟩

end CategoryTheory.Sheaf
