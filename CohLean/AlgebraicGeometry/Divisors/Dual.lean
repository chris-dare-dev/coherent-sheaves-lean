/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.AlgebraicGeometry.Divisors.Determinant
import CohLean.Topology.Opens.CoversTop

/-!
# Sheaf duals and explicit inverses of invertible sheaves

For a module sheaf `M` on a scheme, this file constructs the presheaf
`U ↦ Hom(M|_U, 𝒪_U)`, sheafifies it, and supplies the evaluation map
`M ⊗ Mᵛ → 𝒪_X`.  When `M` is locally free of rank one, evaluation is an
isomorphism: locally it is the ordinary multiplication map `R ⊗[R] R → R`.

Consequently every intrinsic `SheafOfModules.IsInvertible` certificate can be
upgraded to `LineBundleData` with an explicit tensor inverse.  This removes the
need to carry a separate inverse-sheaf certificate when determinant descent has
already proved that its line is locally free of rank one.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable def unitEndRingHom (U : X.Opens) :
    X.presheaf.obj (.op U) →+*
      End (SheafOfModules.unit (X.ringCatSheaf.over U)) where
  toFun r := (SheafOfModules.fullyFaithfulForget
    (X.ringCatSheaf.over U)).preimage
    { app := fun V ↦ by
        letI : CommRing ((X.ringCatSheaf.over U).obj.obj V) :=
          inferInstanceAs (CommRing ((X.sheaf.over U).obj.obj V))
        exact ModuleCat.ofHom
          (LinearMap.lsmul ((X.ringCatSheaf.over U).obj.obj V)
            ((X.ringCatSheaf.over U).obj.obj V)
            ((X.ringCatSheaf.over U).obj.map
              ((initialOpOfTerminal Over.mkIdTerminal).to V) r))
      naturality := fun {V V'} f ↦ by
        letI : CommRing ((X.ringCatSheaf.over U).obj.obj V) :=
          inferInstanceAs (CommRing ((X.sheaf.over U).obj.obj V))
        letI : CommRing ((X.ringCatSheaf.over U).obj.obj V') :=
          inferInstanceAs (CommRing ((X.sheaf.over U).obj.obj V'))
        have hb : (X.ringCatSheaf.over U).obj.map
              ((initialOpOfTerminal Over.mkIdTerminal).to V') r =
            (X.ringCatSheaf.over U).obj.map f
              ((X.ringCatSheaf.over U).obj.map
                ((initialOpOfTerminal Over.mkIdTerminal).to V) r) := by
          rw [← (X.ringCatSheaf.over U).obj.map_comp_apply]
          congr 1
        rw [hb]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        have hs := congrArg (fun q ↦ q x)
          (PresheafOfModules.smul_map
            (M := (SheafOfModules.unit (X.ringCatSheaf.over U)).val) f
              ((X.ringCatSheaf.over U).obj.map
                ((initialOpOfTerminal Over.mkIdTerminal).to V) r))
        exact hs.symm }
  map_one' := by
    apply (SheafOfModules.fullyFaithfulForget
      (X.ringCatSheaf.over U)).map_injective
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (X.ringCatSheaf.over U).obj.map
        ((initialOpOfTerminal Over.mkIdTerminal).to V) 1 *
          (show (X.ringCatSheaf.over U).obj.obj V from x) =
      (show (X.ringCatSheaf.over U).obj.obj V from x)
    have h1 := map_one ((X.ringCatSheaf.over U).obj.map
      ((initialOpOfTerminal Over.mkIdTerminal).to V)).hom
    exact (congrArg (fun z ↦ z *
      (show (X.ringCatSheaf.over U).obj.obj V from x)) h1).trans (one_mul _)
  map_mul' r s := by
    apply (SheafOfModules.fullyFaithfulForget
      (X.ringCatSheaf.over U)).map_injective
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (X.ringCatSheaf.over U).obj.map
        ((initialOpOfTerminal Over.mkIdTerminal).to V) (r * s) *
          (show (X.ringCatSheaf.over U).obj.obj V from x) =
      (X.ringCatSheaf.over U).obj.map
          ((initialOpOfTerminal Over.mkIdTerminal).to V) r *
        ((X.ringCatSheaf.over U).obj.map
          ((initialOpOfTerminal Over.mkIdTerminal).to V) s *
            (show (X.ringCatSheaf.over U).obj.obj V from x))
    have hm := map_mul ((X.ringCatSheaf.over U).obj.map
      ((initialOpOfTerminal Over.mkIdTerminal).to V)).hom r s
    exact (congrArg (fun z ↦ z *
      (show (X.ringCatSheaf.over U).obj.obj V from x)) hm).trans (mul_assoc _ _ _)
  map_zero' := by
    apply (SheafOfModules.fullyFaithfulForget
      (X.ringCatSheaf.over U)).map_injective
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (X.ringCatSheaf.over U).obj.map
        ((initialOpOfTerminal Over.mkIdTerminal).to V) 0 *
          (show (X.ringCatSheaf.over U).obj.obj V from x) = 0
    have h0 := map_zero ((X.ringCatSheaf.over U).obj.map
      ((initialOpOfTerminal Over.mkIdTerminal).to V)).hom
    exact (congrArg (fun z ↦ z *
      (show (X.ringCatSheaf.over U).obj.obj V from x)) h0).trans (zero_mul _)
  map_add' r s := by
    apply (SheafOfModules.fullyFaithfulForget
      (X.ringCatSheaf.over U)).map_injective
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (X.ringCatSheaf.over U).obj.map
        ((initialOpOfTerminal Over.mkIdTerminal).to V) (r + s) *
          (show (X.ringCatSheaf.over U).obj.obj V from x) =
      (X.ringCatSheaf.over U).obj.map
          ((initialOpOfTerminal Over.mkIdTerminal).to V) r *
            (show (X.ringCatSheaf.over U).obj.obj V from x) +
        (X.ringCatSheaf.over U).obj.map
          ((initialOpOfTerminal Over.mkIdTerminal).to V) s *
            (show (X.ringCatSheaf.over U).obj.obj V from x)
    have ha := map_add ((X.ringCatSheaf.over U).obj.map
      ((initialOpOfTerminal Over.mkIdTerminal).to V)).hom r s
    exact (congrArg (fun z ↦ z *
      (show (X.ringCatSheaf.over U).obj.obj V from x)) ha).trans (add_mul _ _ _)

theorem unitEndRingHom_bijective (U : X.Opens) :
    Function.Bijective (unitEndRingHom U) := by
  constructor
  · intro r s hrs
    have h := congrArg (fun q ↦ q.val.app
      (.op (Over.mk (𝟙 U))) (1 : X.presheaf.obj (.op U))) hrs
    simpa [unitEndRingHom] using h
  · intro h
    let r : X.presheaf.obj (.op U) :=
      h.val.app (.op (Over.mk (𝟙 U))) 1
    refine ⟨r, ?_⟩
    apply (SheafOfModules.fullyFaithfulForget
      (X.ringCatSheaf.over U)).map_injective
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let g := (initialOpOfTerminal Over.mkIdTerminal).to V
    have hn := congrArg (fun q ↦ q (1 : X.presheaf.obj (.op U)))
      (h.val.naturality g)
    have h1 : h.val.app V 1 =
        (X.ringCatSheaf.over U).obj.map g r := by
      simpa [r] using hn
    change (X.ringCatSheaf.over U).obj.map g r * x = h.val.app V x
    have hx := (h.val.app V).hom.map_smul x
      (1 : (X.ringCatSheaf.over U).obj.obj V)
    change h.val.app V (x * 1) = x * h.val.app V 1 at hx
    rw [mul_one, h1] at hx
    exact (mul_comm _ _).trans hx.symm

noncomputable def unitEndRingEquiv (U : X.Opens) :
    X.presheaf.obj (.op U) ≃+*
      End (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  RingEquiv.ofBijective (unitEndRingHom U) (unitEndRingHom_bijective U)

@[reducible]
noncomputable def dualSectionModule (M : X.Modules) (U : X.Opens) :
    Module (X.presheaf.obj (.op U))
      (M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  Module.compHom (M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U))
    (unitEndRingHom U)

noncomputable def dualSectionSmul (M : X.Modules) (U : X.Opens)
    (r : X.presheaf.obj (.op U))
    (h : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) := by
  letI := dualSectionModule M U
  exact r • h

noncomputable def dualRestriction (M : X.Modules) {U V : X.Opensᵒᵖ}
    (f : U ⟶ V)
    (h : M.over U.unop ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U.unop)) :
    M.over V.unop ⟶
      SheafOfModules.unit (X.ringCatSheaf.over V.unop) :=
  (SheafOfModules.fullyFaithfulForget
    (X.ringCatSheaf.over V.unop)).preimage
    { app := fun W ↦ h.val.app ((Over.map f.unop).op.obj W)
      naturality := fun {W W'} g ↦ h.val.naturality ((Over.map f.unop).op.map g) }

@[simp]
theorem dualRestriction_add (M : X.Modules) {U V : X.Opensᵒᵖ}
    (f : U ⟶ V)
    (h h' : M.over U.unop ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U.unop)) :
    dualRestriction M f (h + h') =
      dualRestriction M f h + dualRestriction M f h' := by
  apply (SheafOfModules.fullyFaithfulForget
    (X.ringCatSheaf.over V.unop)).map_injective
  ext W x
  rfl

@[simp]
theorem dualRestriction_zero (M : X.Modules) {U V : X.Opensᵒᵖ}
    (f : U ⟶ V) :
    dualRestriction M f 0 = 0 := by
  apply (SheafOfModules.fullyFaithfulForget
    (X.ringCatSheaf.over V.unop)).map_injective
  ext W x
  rfl

theorem dualRestriction_smul (M : X.Modules) {U V : X.Opensᵒᵖ}
    (f : U ⟶ V) (r : X.presheaf.obj U)
    (h : M.over U.unop ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U.unop)) :
    dualRestriction M f (dualSectionSmul M U.unop r h) =
      dualSectionSmul M V.unop (X.presheaf.map f r)
        (dualRestriction M f h) := by
  change dualRestriction M f (h ≫ unitEndRingHom U.unop r) =
    dualRestriction M f h ≫
      unitEndRingHom V.unop (X.presheaf.map f r)
  apply (SheafOfModules.fullyFaithfulForget
    (X.ringCatSheaf.over V.unop)).map_injective
  ext W x
  dsimp [dualRestriction, dualSectionSmul, dualSectionModule,
    unitEndRingHom, SheafOfModules.fullyFaithfulForget,
    SheafOfModules.forget]
  let left :=
    Over.Hom.left ((initialOpOfTerminal Over.mkIdTerminal).to
      ((Over.map f.unop).op.obj W)).unop |>.op
  let right :=
    Over.Hom.left ((initialOpOfTerminal Over.mkIdTerminal).to W).unop |>.op
  have hp : left = f ≫ right := Subsingleton.elim _ _
  have hr : X.sheaf.obj.map left r =
      X.sheaf.obj.map right (X.sheaf.obj.map f r) := by
    rw [hp]
    exact X.sheaf.obj.map_comp_apply f right r
  let y : X.sheaf.obj.obj (.op W.unop.left) :=
    h.val.app ((Over.map f.unop).op.obj W) x
  change (show X.sheaf.obj.obj (.op W.unop.left) from
      X.sheaf.obj.map left r) * y =
    X.sheaf.obj.map right (X.sheaf.obj.map f r) * y
  exact congrArg (fun z ↦ z * y) hr

noncomputable def dualPresheaf (M : X.Modules) : X.PresheafOfModules where
  obj U := by
    letI := dualSectionModule M U.unop
    exact ModuleCat.of (X.presheaf.obj U)
      (M.over U.unop ⟶
        SheafOfModules.unit (X.ringCatSheaf.over U.unop))
  map {U V} f := by
    letI := dualSectionModule M U.unop
    letI := dualSectionModule M V.unop
    let target := ModuleCat.of (X.presheaf.obj V)
      (M.over V.unop ⟶
        SheafOfModules.unit (X.ringCatSheaf.over V.unop))
    exact ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (X.presheaf.map f).hom).obj target)
      { toFun := dualRestriction M f
        map_add' := dualRestriction_add M f
        map_smul' := dualRestriction_smul M f }
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    apply (SheafOfModules.fullyFaithfulForget
      (X.ringCatSheaf.over U.unop)).map_injective
    ext W x
    rfl
  map_comp {U V W} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    apply (SheafOfModules.fullyFaithfulForget
      (X.ringCatSheaf.over W.unop)).map_injective
    ext Z x
    rfl

noncomputable def dualEvaluationApp (M : X.Modules) (U : X.Opensᵒᵖ) :
    M.val.obj U ⊗ (dualPresheaf M).obj U ⟶
      (PresheafOfModules.unit X.presheaf).obj U :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun m h ↦ h.val.app (.op (Over.mk (𝟙 U.unop))) m)
    (fun m m' h ↦ by
      change h.val.app (.op (Over.mk (𝟙 U.unop))) (m + m') = _
      rw [map_add])
    (fun r m h ↦ by
      change h.val.app (.op (Over.mk (𝟙 U.unop))) (r • m) = _
      rw [map_smul]
      rfl)
    (fun m h h' ↦ by
      change (h + h').val.app (.op (Over.mk (𝟙 U.unop))) m = _
      rfl)
    (fun r m h ↦ by
      change (dualSectionSmul M U.unop r h).val.app
          (.op (Over.mk (𝟙 U.unop))) m = _
      dsimp [dualSectionSmul, dualSectionModule, unitEndRingHom]
      change h.val.app (.op (Over.mk (𝟙 U.unop))) m * r =
        r * h.val.app (.op (Over.mk (𝟙 U.unop))) m
      rw [mul_comm])

noncomputable def dualEvaluation (M : X.Modules) :
    M.val ⊗ dualPresheaf M ⟶ PresheafOfModules.unit X.presheaf where
  app U := dualEvaluationApp M U
  naturality {U V} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m h
    change h.val.app ((Over.map f.unop).op.obj (.op (Over.mk (𝟙 V.unop))))
        (M.val.map f m) =
      X.presheaf.map f (h.val.app (.op (Over.mk (𝟙 U.unop))) m)
    let g : (.op (Over.mk (𝟙 U.unop))) ⟶
        (Over.map f.unop).op.obj (.op (Over.mk (𝟙 V.unop))) :=
      (Over.homMk f.unop).op
    have hn := h.val.naturality g
    exact congrArg (fun q ↦ q m) hn

noncomputable def dualCoordinateEquiv (M : X.Modules) (U : X.Opens)
    (e : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ M.over U) :
    letI := dualSectionModule M U
    (M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) ≃ₗ[
      X.presheaf.obj (.op U)] X.presheaf.obj (.op U) := by
  letI := dualSectionModule M U
  let E := unitEndRingEquiv U
  exact
    { toFun := fun h ↦ E.symm (e.hom ≫ h)
      invFun := fun r ↦ e.inv ≫ unitEndRingHom U r
      map_add' := fun h h' ↦ by
        rw [← E.symm.map_add]
        congr 1
        simp
      map_smul' := fun r h ↦ by
        apply E.injective
        change e.hom ≫ (h ≫ unitEndRingHom U r) =
          unitEndRingHom U (r * E.symm (e.hom ≫ h))
        rw [E.map_mul, E.apply_symm_apply]
        change e.hom ≫ h ≫ unitEndRingHom U r =
          (e.hom ≫ h) * unitEndRingHom U r
        rfl
      left_inv := fun h ↦ by
        change e.inv ≫ unitEndRingHom U (E.symm (e.hom ≫ h)) = h
        rw [show unitEndRingHom U = E.toRingHom from rfl, E.apply_symm_apply]
        simp
      right_inv := fun r ↦ by
        change E.symm (e.hom ≫ e.inv ≫ unitEndRingHom U r) = r
        simp [show unitEndRingHom U = E.toRingHom from rfl] }

noncomputable def dualEvaluationIsoOfTrivialization (M : X.Modules)
    (U : X.Opens)
    (e : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ M.over U) :
    M.val.obj (.op U) ⊗ (dualPresheaf M).obj (.op U) ≅
      (PresheafOfModules.unit X.presheaf).obj (.op U) := by
  letI := dualSectionModule M U
  let eU : ModuleCat.of (X.presheaf.obj (.op U))
        (X.presheaf.obj (.op U)) ≅ M.val.obj (.op U) :=
    ((SheafOfModules.fullyFaithfulForget
      (X.ringCatSheaf.over U)).mapIso e).app (.op (Over.mk (𝟙 U)))
  exact MonoidalCategory.tensorIso eU.symm
      (dualCoordinateEquiv M U e).toModuleIso ≪≫
    λ_ (ModuleCat.of (X.presheaf.obj (.op U))
      (X.presheaf.obj (.op U)))

theorem dualEvaluationIsoOfTrivialization_hom (M : X.Modules)
    (U : X.Opens)
    (e : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ M.over U) :
    (dualEvaluationIsoOfTrivialization M U e).hom =
      dualEvaluationApp M (.op U) := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m h
  dsimp [dualEvaluationIsoOfTrivialization, dualEvaluationApp]

theorem dualEvaluationApp_isIso_of_trivialization (M : X.Modules)
    (U : X.Opens)
    (e : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ M.over U) :
    IsIso (dualEvaluationApp M (.op U)) := by
  rw [← dualEvaluationIsoOfTrivialization_hom M U e]
  infer_instance

def rankOneTrivializingBasis {M : X.Modules}
    (q : (show SheafOfModules X.ringCatSheaf from M).LocalGeneratorsData) :
    Set X.Opens :=
  { U | ∃ i, U ≤ q.X i }

theorem rankOneTrivializingBasis_isBasis {M : X.Modules}
    (q : (show SheafOfModules X.ringCatSheaf from M).LocalGeneratorsData) :
    TopologicalSpace.Opens.IsBasis (rankOneTrivializingBasis q) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U x hxU
  have hsup : ⨆ i, q.X i = ⊤ :=
    (_root_.Opens.coversTop_iff (X : Type u) q.X).mp q.coversTop
  have hxTop : x ∈ (⊤ : X.Opens) := by simp
  rw [← hsup, TopologicalSpace.Opens.mem_iSup] at hxTop
  obtain ⟨i, hxi⟩ := hxTop
  refine ⟨U ⊓ q.X i, ⟨i, inf_le_right⟩, ?_, inf_le_left⟩
  exact ⟨hxU, hxi⟩

theorem dualEvaluation_W_of_rankOneData {M : X.Modules}
    (q : (show SheafOfModules X.ringCatSheaf from M).LocalGeneratorsData)
    [q.IsLocallyFreeData] (hq : q.IsRankOne) :
    (_root_.Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf X.presheaf).map (dualEvaluation M)) := by
  apply TopCat.Presheaf.grothendieckTopology_W_of_isIso_app_of_isBasis
    (rankOneTrivializingBasis_isBasis q)
  intro U hU
  obtain ⟨i, hUi⟩ := hU
  let e := q.rankOneTrivializationOver hq i (homOfLE hUi)
  haveI : IsIso (dualEvaluationApp M (.op U)) :=
    dualEvaluationApp_isIso_of_trivialization M U e
  change IsIso ((forget₂ (ModuleCat (X.presheaf.obj (.op U)))
    AddCommGrpCat).map (dualEvaluationApp M (.op U)))
  infer_instance

private abbrev dualAssociatedSheaf (X : Scheme.{u}) :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/-- The sheaf dual of a module sheaf, constructed from local morphisms into the
structure sheaf and then sheafified. -/
noncomputable def dualObj (M : X.Modules) : X.Modules :=
  (dualAssociatedSheaf X).obj (dualPresheaf M)

noncomputable def sheafifiedDualEvaluation (M : X.Modules) :
    (dualAssociatedSheaf X).obj (M.val ⊗ dualPresheaf M) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  (dualAssociatedSheaf X).map (dualEvaluation M) ≫
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.app
        (SheafOfModules.unit X.ringCatSheaf)

theorem sheafifiedDualEvaluation_isIso_of_rankOneData {M : X.Modules}
    (q : (show SheafOfModules X.ringCatSheaf from M).LocalGeneratorsData)
    [q.IsLocallyFreeData] (hq : q.IsRankOne) :
    IsIso (sheafifiedDualEvaluation M) := by
  haveI : IsIso ((dualAssociatedSheaf X).map (dualEvaluation M)) := by
    apply Localization.inverts (dualAssociatedSheaf X)
      ((_root_.Opens.grothendieckTopology X).W.inverseImage
        (PresheafOfModules.toPresheaf X.presheaf))
    exact dualEvaluation_W_of_rankOneData q hq
  dsimp [sheafifiedDualEvaluation]
  infer_instance

theorem sheafifiedDualEvaluation_isIso (M : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)] :
    IsIso (sheafifiedDualEvaluation M) := by
  obtain ⟨q, hq, hrank⟩ :=
    SheafOfModules.IsInvertible.exists_rankOneData
      (M := show SheafOfModules X.ringCatSheaf from M)
  letI : q.IsLocallyFreeData := hq
  exact sheafifiedDualEvaluation_isIso_of_rankOneData q hrank

attribute [instance] sheafifiedDualEvaluation_isIso

noncomputable def tensorDualEvaluation (M : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)] :
    tensorObj M (dualObj M) ⟶ SheafOfModules.unit X.ringCatSheaf :=
  inv (tensorSheafificationComparisonLeft M (dualPresheaf M)) ≫
    sheafifiedDualEvaluation M

theorem tensorDualEvaluation_isIso (M : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)] :
    IsIso (tensorDualEvaluation M) := by
  dsimp [tensorDualEvaluation]
  infer_instance

attribute [instance] tensorDualEvaluation_isIso

noncomputable def tensorOverComparisonIso (L N : X.Modules) (U : X.Opens) :
    letI : MonoidalCategory
        (_root_.PresheafOfModules.{u} (X.ringCatSheaf.over U).obj) :=
      PresheafOfModules.monoidalCategory (R := (X.sheaf.over U).obj)
    (PresheafOfModules.sheafification
      (𝟙 (X.ringCatSheaf.over U).obj)).obj
        ((L.over U).val ⊗ (N.over U).val) ≅
      (tensorObj L N).over U := by
  let aU := PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)
  exact aU.mapIso (overTensorPresheafIso L.val N.val U).symm ≪≫
    asIso (overSheafificationComparison (L.val ⊗ N.val) U)

noncomputable def tensorWithTrivializedLeftIso (L N : X.Modules)
    (U : X.Opens)
    (e : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ L.over U) :
    N.over U ≅ (tensorObj L N).over U := by
  letI : MonoidalCategory
      (_root_.PresheafOfModules.{u} (X.ringCatSheaf.over U).obj) :=
    PresheafOfModules.monoidalCategory (R := (X.sheaf.over U).obj)
  let aU := PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)
  let eP := (SheafOfModules.fullyFaithfulForget
    (X.ringCatSheaf.over U)).mapIso e
  exact (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (X.ringCatSheaf.over U).obj)).counit.app (N.over U)).symm ≪≫
    aU.mapIso (λ_ (N.over U).val).symm ≪≫
    aU.mapIso (MonoidalCategory.tensorIso eP (Iso.refl _)) ≪≫
    tensorOverComparisonIso L N U

noncomputable def dualObjTrivialization (M : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)]
    (U : X.Opens)
    (e : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ M.over U) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ≅ (dualObj M).over U :=
  ((tensorWithTrivializedLeftIso M (dualObj M) U e) ≪≫
      (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso
        (asIso (tensorDualEvaluation M)) ≪≫
      (SheafOfModules.overUnitIso U).symm).symm

theorem dualObj_isInvertible (M : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)] :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from dualObj M) := by
  obtain ⟨q, hq, hrank⟩ :=
    SheafOfModules.IsInvertible.exists_rankOneData
      (M := show SheafOfModules X.ringCatSheaf from M)
  letI : q.IsLocallyFreeData := hq
  apply SheafOfModules.IsInvertible.of_trivializations q.X q.coversTop
  intro i
  exact dualObjTrivialization M (q.X i) (q.rankOneTrivialization hrank i)

attribute [instance] dualObj_isInvertible

/-- Every intrinsically invertible sheaf has a canonical explicit tensor inverse,
given by its sheaf dual. -/
noncomputable def LineBundleData.ofIsInvertible (M : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)] : LineBundleData X where
  line := M
  inverse := dualObj M
  lineIsInvertible := inferInstance
  inverseIsInvertible := dualObj_isInvertible M
  tensorInverseIso := asIso (tensorDualEvaluation M)

@[simp]
theorem LineBundleData.ofIsInvertible_line (M : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)] :
    (LineBundleData.ofIsInvertible M).line = M := rfl

end AlgebraicGeometry.Scheme.Modules

