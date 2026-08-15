/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.StabilityFunction.PhaseGeometry

/-!
# First uniqueness lemmas for owner HN filtrations

This file starts the owner-native uniqueness argument with its normalization
and semistable base cases.  Later leaves build the descent and tail-filtration
steps on this interface.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

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

namespace Subobject

omit [Abelian A] in
/-- Mapping a subobject along a monomorphism agrees with the subobject
represented by the composite arrow. -/
theorem map_eq_mk_mono {X Y : A} (f : X ⟶ Y) [Mono f] (S : Subobject X) :
    (Subobject.map f).obj S = Subobject.mk (S.arrow ≫ f) := by
  calc
    (Subobject.map f).obj S = (Subobject.map f).obj (Subobject.mk S.arrow) := by
      rw [Subobject.mk_arrow]
    _ = Subobject.mk (S.arrow ≫ f) := by
      simpa using Subobject.map_mk S.arrow f

/-- A subobject and its image under a monomorphism have canonically
isomorphic underlying objects. -/
noncomputable def mapMonoIso {X Y : A} (f : X ⟶ Y) [Mono f]
    (S : Subobject X) : ((Subobject.map f).obj S : A) ≅ (S : A) :=
  Subobject.isoOfEqMk _ (S.arrow ≫ f) (map_eq_mk_mono f S)

omit [Abelian A] in
theorem ofLE_map_comp_mapMonoIso_hom {X Y : A} (f : X ⟶ Y) [Mono f]
    {S T : Subobject X} (h : S ≤ T) :
    Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
        ((Subobject.map f).monotone h) ≫ (mapMonoIso f T).hom =
      (mapMonoIso f S).hom ≫ Subobject.ofLE S T h := by
  apply Subobject.eq_of_comp_arrow_eq
  apply (cancel_mono f).1
  simp [mapMonoIso, Category.assoc]

/-- Successive quotients are unchanged when a subobject chain is mapped
along a monomorphism. -/
noncomputable def cokernelMapMonoIso {X Y : A} (f : X ⟶ Y) [Mono f]
    {S T : Subobject X} (h : S ≤ T) :
    cokernel (Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
      ((Subobject.map f).monotone h)) ≅
      cokernel (Subobject.ofLE S T h) :=
  cokernel.mapIso _ _ (mapMonoIso f S) (mapMonoIso f T)
    (by simpa [Category.assoc] using ofLE_map_comp_mapMonoIso_hom f h)

end Subobject

theorem phase_cokernel_mapMono_eq (Z : StabilityFunction A) {X Y : A}
    (f : X ⟶ Y) [Mono f] {S T : Subobject X} (h : S ≤ T) :
    Z.phase (cokernel (Subobject.ofLE ((Subobject.map f).obj S)
      ((Subobject.map f).obj T) ((Subobject.map f).monotone h))) =
      Z.phase (cokernel (Subobject.ofLE S T h)) :=
  Z.phase_eq_of_iso (Subobject.cokernelMapMonoIso f h)

theorem isSemistable_cokernel_mapMono_iff (Z : StabilityFunction A)
    {X Y : A} (f : X ⟶ Y) [Mono f] {S T : Subobject X} (h : S ≤ T) :
    Z.IsSemistable (cokernel (Subobject.ofLE ((Subobject.map f).obj S)
      ((Subobject.map f).obj T) ((Subobject.map f).monotone h))) ↔
      Z.IsSemistable (cokernel (Subobject.ofLE S T h)) := by
  constructor
  · exact Z.isSemistable_of_iso (Subobject.cokernelMapMonoIso f h)
  · exact Z.isSemistable_of_iso (Subobject.cokernelMapMonoIso f h).symm

/-- Append a lower-phase semistable quotient to an owner abelian HN
filtration along a monomorphism. -/
theorem append_hn_filtration_of_mono (Z : StabilityFunction A) {X Y B : A}
    (i : X ⟶ Y) [Mono i] (F : AbelianHNFiltration Z X)
    (eB : cokernel i ≅ B) (hB : Z.IsSemistable B)
    (hlast : Z.phase B < F.phase ⟨F.n - 1, by have := F.nonempty; omega⟩) :
    ∃ G : AbelianHNFiltration Z Y,
      G.phase ⟨G.n - 1, by have := G.nonempty; omega⟩ = Z.phase B := by
  let K : Subobject Y := Subobject.mk i
  let eK : cokernel K.arrow ≅ B := by
    let eKi : cokernel K.arrow ≅ cokernel i := by
      refine cokernel.mapIso (f := K.arrow) (f' := i)
        (Subobject.underlyingIso i) (Iso.refl _) ?_
      calc
        K.arrow ≫ (Iso.refl Y).hom = K.arrow := by simp
        _ = (Subobject.underlyingIso i).hom ≫ i := by
          exact (Subobject.underlyingIso_hom_comp_eq_mk i).symm
    exact eKi ≪≫ eB
  have hK_ne_top : K ≠ ⊤ := by
    intro hK
    have hmk : Subobject.mk i = ⊤ := by simpa [K] using hK
    haveI : IsIso i := (Subobject.isIso_iff_mk_eq_top i).2 hmk
    exact hB.1 ((isZero_cokernel_of_epi i).of_iso eB.symm)
  have hK_lt_top : K < ⊤ := lt_of_le_of_ne le_top hK_ne_top
  let newChain : Fin (F.n + 2) → Subobject Y := fun j ↦
    if h : (j : ℕ) ≤ F.n then
      (Subobject.map i).obj (F.chain ⟨j, by omega⟩)
    else ⊤
  have hNewBot : newChain ⟨0, by omega⟩ = ⊥ := by
    change (Subobject.map i).obj (F.chain ⟨0, by omega⟩) = ⊥
    rw [F.chain_bot]
    exact Subobject.map_bot i
  have hNewK : newChain ⟨F.n, by omega⟩ = K := by
    simp [newChain, K, Subobject.map_top, F.chain_top]
  have hNewTop : newChain ⟨F.n + 1, by omega⟩ = ⊤ := by
    simp [newChain]
  have hNewMono : StrictMono newChain := by
    apply Fin.strictMono_iff_lt_succ.mpr
    rintro ⟨j, hj⟩
    change newChain ⟨j, by omega⟩ < newChain ⟨j + 1, by omega⟩
    by_cases hjn : j = F.n
    · subst hjn
      rw [hNewK, hNewTop]
      exact hK_lt_top
    · have hjle : j + 1 ≤ F.n := by omega
      simp [newChain, show j ≤ F.n by omega, hjle]
      apply (Subobject.map i).monotone.strictMono_of_injective
        (Subobject.map_obj_injective i)
      exact F.chain_strictMono (Fin.mk_lt_mk.mpr (by omega))
  let phase : Fin (F.n + 1) → ℝ := fun j ↦
    if h : (j : ℕ) < F.n then F.phase ⟨j, h⟩ else Z.phase B
  refine ⟨{
    n := F.n + 1
    nonempty := Nat.succ_pos _
    chain := newChain
    chain_strictMono := hNewMono
    chain_bot := hNewBot
    chain_top := hNewTop
    phase := phase
    phase_strictAnti := ?_
    factor_phase := ?_
    factor_semistable := ?_
  }, ?_⟩
  · intro a b hab
    dsimp [phase]
    by_cases hb : (b : ℕ) < F.n
    · have ha : (a : ℕ) < F.n := (Fin.mk_lt_mk.mp hab).trans hb
      simp [ha, hb]
      exact F.phase_strictAnti (Fin.mk_lt_mk.mpr (Fin.mk_lt_mk.mp hab))
    · have ha : (a : ℕ) < F.n := by omega
      have hlast_le : F.phase ⟨F.n - 1, by omega⟩ ≤ F.phase ⟨a, ha⟩ :=
        F.phase_strictAnti.antitone (Fin.mk_le_mk.mpr (by omega))
      simp [ha, hb]
      exact hlast.trans_le hlast_le
  · intro j
    by_cases hj : (j : ℕ) < F.n
    · let j' : Fin F.n := ⟨j, hj⟩
      have hcast : newChain j.castSucc =
          (Subobject.map i).obj (F.chain j'.castSucc) := by
        simp [newChain, j', show (j : ℕ) ≤ F.n by omega]
      have hsucc : newChain j.succ =
          (Subobject.map i).obj (F.chain j'.succ) := by
        simp [newChain, j', show (j : ℕ) + 1 ≤ F.n by omega]
      have hp := (Z.phase_cokernel_mapMono_eq i
        (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))).trans
        (F.factor_phase j')
      exact ((Z.phase_cokernel_ofLE_congr hcast hsucc).trans hp).trans (by
        simp [phase, hj, j'])
    · have hj_eq : (j : ℕ) = F.n := by omega
      have hcast : j.castSucc = ⟨F.n, by omega⟩ := Fin.ext hj_eq
      have hsucc : j.succ = ⟨F.n + 1, by omega⟩ := Fin.ext (by simp [hj_eq])
      have hcast_obj : newChain j.castSucc = K := hcast ▸ hNewK
      have hsucc_obj : newChain j.succ = ⊤ := hsucc ▸ hNewTop
      have htarget : Z.phase (cokernel (Subobject.ofLE K ⊤ le_top)) =
          Z.phase B := by
        calc
          Z.phase (cokernel (Subobject.ofLE K ⊤ le_top)) =
              Z.phase (cokernel K.arrow) :=
            Z.phase_eq_of_iso
              ((cokernelIsoOfEq (Subobject.ofLE_arrow _).symm ≪≫
                cokernelCompIsIso _ _).symm)
          _ = Z.phase B := Z.phase_eq_of_iso eK
      exact ((Z.phase_cokernel_ofLE_congr hcast_obj hsucc_obj).trans htarget).trans (by
        simp [phase, hj])
  · intro j
    by_cases hj : (j : ℕ) < F.n
    · let j' : Fin F.n := ⟨j, hj⟩
      have hcast : newChain j.castSucc =
          (Subobject.map i).obj (F.chain j'.castSucc) := by
        simp [newChain, j', show (j : ℕ) ≤ F.n by omega]
      have hsucc : newChain j.succ =
          (Subobject.map i).obj (F.chain j'.succ) := by
        simp [newChain, j', show (j : ℕ) + 1 ≤ F.n by omega]
      have hs := (Z.isSemistable_cokernel_mapMono_iff i
        (le_of_lt (F.chain_strictMono j'.castSucc_lt_succ))).2
        (F.factor_semistable j')
      exact Z.isSemistable_cokernel_ofLE_congr hcast hsucc hs
    · have hj_eq : (j : ℕ) = F.n := by omega
      have hcast : j.castSucc = ⟨F.n, by omega⟩ := Fin.ext hj_eq
      have hsucc : j.succ = ⟨F.n + 1, by omega⟩ := Fin.ext (by simp [hj_eq])
      have hcast_obj : newChain j.castSucc = K := hcast ▸ hNewK
      have hsucc_obj : newChain j.succ = ⊤ := hsucc ▸ hNewTop
      let eTop : B ≅ cokernel (Subobject.ofLE K ⊤ le_top) :=
        eK.symm ≪≫
          (cokernelIsoOfEq (Subobject.ofLE_arrow _).symm ≪≫ cokernelCompIsIso _ _)
      exact Z.isSemistable_cokernel_ofLE_congr hcast_obj hsucc_obj
        (Z.isSemistable_of_iso eTop hB)
  · simp [phase]

/-- The one-factor owner HN filtration of a semistable abelian object. -/
theorem exists_hn_with_last_phase_of_semistable (Z : StabilityFunction A)
    {E : A} (hE : Z.IsSemistable E) :
    ∃ F : AbelianHNFiltration Z E,
      F.phase ⟨F.n - 1, by have := F.nonempty; omega⟩ = Z.phase E := by
  refine ⟨{
    n := 1
    nonempty := Nat.one_pos
    chain := fun i ↦ if i = 0 then ⊥ else ⊤
    chain_strictMono := ?_
    chain_bot := by simp
    chain_top := by simp
    phase := fun _ ↦ Z.phase E
    phase_strictAnti := fun a b hab ↦ (by omega)
    factor_phase := ?_
    factor_semistable := ?_
  }, by simp⟩
  · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [Fin.lt_def] at hij
    have hi0 : i = 0 := by omega
    have hj1 : j = 1 := by omega
    subst hi0
    subst hj1
    simp only [Fin.zero_eta, Fin.mk_one, one_ne_zero, if_false, if_true]
    exact lt_of_le_of_ne bot_le
      (Ne.symm (StabilityFunction.subobject_top_ne_bot_of_not_isZero hE.1))
  · intro ⟨j, hj⟩
    have hj0 : j = 0 := by omega
    subst hj0
    change Z.phase (cokernel (Subobject.ofLE ⊥ ⊤ _)) = Z.phase E
    rw [Z.phase_eq_of_iso (StabilityFunction.subobjectCokernelBotIso ⊤ bot_le)]
    exact Z.phase_eq_of_iso (asIso (⊤ : Subobject E).arrow)
  · intro ⟨j, hj⟩
    have hj0 : j = 0 := by omega
    subst hj0
    change Z.IsSemistable (cokernel (Subobject.ofLE ⊥ ⊤ _))
    exact Z.isSemistable_of_iso
      ((asIso (⊤ : Subobject E).arrow).symm ≪≫
        (StabilityFunction.subobjectCokernelBotIso ⊤ bot_le).symm) hE

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

/-- If a subobject maps trivially to the quotient by another subobject, it is
contained in that subobject. -/
theorem le_of_arrow_comp_cokernel_zero {E : A} {B M : Subobject E}
    (h : B.arrow ≫ cokernel.π M.arrow = 0) : B ≤ M := by
  have hkernel : kernelSubobject (cokernel.π M.arrow) = M := by
    simpa [imageSubobject_mono, Subobject.mk_arrow] using
      ((ShortComplex.mk M.arrow (cokernel.π M.arrow)
        (cokernel.condition M.arrow)).exact_iff_image_eq_kernel.mp
        (ShortComplex.exact_cokernel M.arrow)).symm
  rw [← hkernel]
  exact Subobject.le_of_comm
    (factorThruKernelSubobject _ B.arrow h)
    (factorThruKernelSubobject_comp_arrow _ _ _)

/-- The relative form of `le_of_arrow_comp_cokernel_zero`: a subobject of `S`
that maps trivially to the quotient `S / M` is contained in `M`. -/
theorem le_of_ofLE_comp_cokernel_zero {E : A} {B M S : Subobject E}
    (hBS : B ≤ S) (hMS : M ≤ S)
    (h : Subobject.ofLE B S hBS ≫
      cokernel.π (Subobject.ofLE M S hMS) = 0) : B ≤ M := by
  have hse : (ShortComplex.mk (Subobject.ofLE M S hMS)
      (cokernel.π (Subobject.ofLE M S hMS))
      (cokernel.condition _)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _)
      inferInstance inferInstance
  set g := hse.fIsKernel.lift (KernelFork.ofι (Subobject.ofLE B S hBS) h)
  have hg : g ≫ Subobject.ofLE M S hMS = Subobject.ofLE B S hBS :=
    hse.fIsKernel.fac (KernelFork.ofι (Subobject.ofLE B S hBS) h)
      WalkingParallelPair.zero
  apply Subobject.le_of_comm g
  calc
    g ≫ M.arrow = g ≫ (Subobject.ofLE M S hMS ≫ S.arrow) := by
      congr 1
      exact (Subobject.ofLE_arrow hMS).symm
    _ = (g ≫ Subobject.ofLE M S hMS) ≫ S.arrow :=
      (Category.assoc _ _ _).symm
    _ = Subobject.ofLE B S hBS ≫ S.arrow := by congr 1
    _ = B.arrow := Subobject.ofLE_arrow hBS

/-- Pulling bottom back along the quotient by a subobject recovers the
subobject. -/
theorem pullback_cokernel_bot_eq {E : A} (M : Subobject E) :
    (Subobject.pullback (cokernel.π M.arrow)).obj ⊥ = M := by
  apply le_antisymm
  · let P := (Subobject.pullback (cokernel.π M.arrow)).obj ⊥
    have hP : P.arrow ≫ cokernel.π M.arrow = 0 := by
      have h := (Subobject.isPullback (cokernel.π M.arrow)
        (⊥ : Subobject (cokernel M.arrow))).w
      simp only [Subobject.bot_arrow, comp_zero] at h
      exact h.symm
    exact le_of_arrow_comp_cokernel_zero hP
  · exact Subobject.le_of_comm
      ((Subobject.isPullback (cokernel.π M.arrow) (⊥ : Subobject _)).isLimit.lift
        (PullbackCone.mk 0 M.arrow (by simp [cokernel.condition])))
      ((Subobject.isPullback (cokernel.π M.arrow) (⊥ : Subobject _)).isLimit.fac _
        WalkingCospan.right)

/-- Quotienting by a nonzero subobject strictly decreases a finite subobject
lattice. -/
theorem card_subobject_cokernel_lt {E : A} {M : Subobject E}
    (hM : M ≠ ⊥) [Finite (Subobject E)] :
    Nat.card (Subobject (cokernel M.arrow)) < Nat.card (Subobject E) := by
  haveI := Fintype.ofFinite (Subobject E)
  haveI : Finite (Subobject (cokernel M.arrow)) :=
    Finite.of_injective _ (StabilityFunction.pullback_obj_injective_of_epi
      (cokernel.π M.arrow))
  haveI := Fintype.ofFinite (Subobject (cokernel M.arrow))
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_of_notMem
    (Subobject.pullback (cokernel.π M.arrow)).obj
    (StabilityFunction.pullback_obj_injective_of_epi _)
    (by
      simp only [Set.mem_range, not_exists]
      intro B hB
      apply hM
      apply le_bot_iff.mp
      calc
        M = (Subobject.pullback (cokernel.π M.arrow)).obj ⊥ :=
          (pullback_cokernel_bot_eq M).symm
        _ ≤ (Subobject.pullback (cokernel.π M.arrow)).obj B :=
          Functor.monotone _ bot_le
        _ = ⊥ := hB)

/-- Every subobject of a quotient pulls back to a subobject containing the
kernel of the quotient map. -/
theorem le_pullback_cokernel {E : A} (M : Subobject E)
    (B : Subobject (cokernel M.arrow)) :
    M ≤ (Subobject.pullback (cokernel.π M.arrow)).obj B :=
  (pullback_cokernel_bot_eq M).symm.le.trans
    (Functor.monotone _ bot_le)

/-- The kernel inclusion followed by the restricted quotient map is zero. -/
theorem ofLE_pullbackπ_cokernel_eq_zero {E : A} (M : Subobject E)
    (B : Subobject (cokernel M.arrow)) :
    Subobject.ofLE M _ (le_pullback_cokernel M B) ≫
      Subobject.pullbackπ (cokernel.π M.arrow) B = 0 := by
  apply (cancel_mono B.arrow).mp
  simp only [zero_comp, Category.assoc]
  have hw := (Subobject.isPullback (cokernel.π M.arrow) B).w
  calc
    Subobject.ofLE M _ (le_pullback_cokernel M B) ≫
        (Subobject.pullbackπ (cokernel.π M.arrow) B ≫ B.arrow) =
        Subobject.ofLE M _ (le_pullback_cokernel M B) ≫
          (((Subobject.pullback (cokernel.π M.arrow)).obj B).arrow ≫
            cokernel.π M.arrow) := by rw [hw]
    _ = (Subobject.ofLE M _ (le_pullback_cokernel M B) ≫
          ((Subobject.pullback (cokernel.π M.arrow)).obj B).arrow) ≫
            cokernel.π M.arrow := by rw [Category.assoc]
    _ = M.arrow ≫ cokernel.π M.arrow := by rw [Subobject.ofLE_arrow]
    _ = 0 := cokernel.condition M.arrow

/-- Pulling a subobject of a quotient back gives a canonical short exact
sequence with the quotient kernel. -/
theorem shortExact_ofLE_pullbackπ_cokernel {E : A} (M : Subobject E)
    (B : Subobject (cokernel M.arrow)) :
    (ShortComplex.mk
      (Subobject.ofLE M _ (le_pullback_cokernel M B))
      (Subobject.pullbackπ (cokernel.π M.arrow) B)
      (ofLE_pullbackπ_cokernel_eq_zero M B)).ShortExact := by
  let p := cokernel.π M.arrow
  let pbB := (Subobject.pullback p).obj B
  let hle := le_pullback_cokernel M B
  let hcomp := ofLE_pullbackπ_cokernel_eq_zero M B
  have hquotient :
      (ShortComplex.mk M.arrow p (cokernel.condition M.arrow)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel M.arrow)
      inferInstance inferInstance
  have hkernel := hquotient.fIsKernel
  haveI : Epi (Subobject.pullbackπ p B) := by
    rw [← (Subobject.isPullback p B).isoPullback_hom_fst]
    infer_instance
  apply ShortComplex.ShortExact.mk' _ inferInstance inferInstance
  apply ShortComplex.exact_of_f_is_kernel
  have hw := (Subobject.isPullback p B).w
  have key : ∀ {W : A} (g : W ⟶ (pbB : A)),
      g ≫ Subobject.pullbackπ p B = 0 → (g ≫ pbB.arrow) ≫ p = 0 := by
    intro W g hg
    calc
      (g ≫ pbB.arrow) ≫ p = g ≫ (pbB.arrow ≫ p) := by rw [Category.assoc]
      _ = g ≫ (Subobject.pullbackπ p B ≫ B.arrow) := by rw [hw]
      _ = (g ≫ Subobject.pullbackπ p B) ≫ B.arrow := by rw [← Category.assoc]
      _ = 0 := by rw [hg, zero_comp]
  exact KernelFork.IsLimit.ofι' (Subobject.ofLE M pbB hle) hcomp
    (fun g hg => ⟨hkernel.lift (KernelFork.ofι (g ≫ pbB.arrow) (key g hg)), by
      apply (cancel_mono pbB.arrow).mp
      rw [Category.assoc, Subobject.ofLE_arrow]
      exact hkernel.fac (KernelFork.ofι (g ≫ pbB.arrow) (key g hg))
        WalkingParallelPair.zero⟩)

/-- The charge of a pulled-back quotient subobject is the sum of the kernel
charge and the subobject charge. -/
theorem charge_pullback_eq_add (Z : StabilityFunction A) {E : A}
    (M : Subobject E) (B : Subobject (cokernel M.arrow)) :
    Z.charge (((Subobject.pullback (cokernel.π M.arrow)).obj B) : A) =
      Z.charge (M : A) + Z.charge (B : A) :=
  Z.additive _ (shortExact_ofLE_pullbackπ_cokernel M B)

/-- Pulling the image of a subobject containing the quotient kernel back along
the quotient projection recovers the original subobject. -/
theorem pullback_imageSubobject_eq (Z : StabilityFunction A) {E : A}
    {M S : Subobject E} (hMS : M ≤ S) :
    (Subobject.pullback (cokernel.π M.arrow)).obj
      (imageSubobject (S.arrow ≫ cokernel.π M.arrow)) = S := by
  let p := cokernel.π M.arrow
  let I := imageSubobject (S.arrow ≫ p)
  let pbI := (Subobject.pullback p).obj I
  change pbI = S
  have hle : S ≤ pbI := Subobject.le_of_comm
    ((Subobject.isPullback p I).isLimit.lift
      (PullbackCone.mk (factorThruImageSubobject (S.arrow ≫ p)) S.arrow
        (imageSubobject_arrow_comp (f := S.arrow ≫ p))))
    ((Subobject.isPullback p I).isLimit.fac _ WalkingCospan.right)
  have hpb := charge_pullback_eq_add Z M I
  have hS := Z.additive _
    (ShortComplex.ShortExact.mk'
      (ShortComplex.exact_cokernel (Subobject.ofLE M S hMS))
      inferInstance inferInstance)
  have hI : Z.charge (I : A) =
      Z.charge (cokernel (Subobject.ofLE M S hMS)) := by
    have hses := Z.additive _
      (ShortComplex.ShortExact.mk'
        (ShortComplex.exact_cokernel (kernel.ι (S.arrow ≫ p)))
        inferInstance inferInstance)
    have hcondition : Subobject.ofLE M S hMS ≫ (S.arrow ≫ p) = 0 := by
      rw [← Category.assoc, Subobject.ofLE_arrow]
      exact cokernel.condition M.arrow
    have hkernelCondition :
        (kernel.ι (S.arrow ≫ p) ≫ S.arrow) ≫ cokernel.π M.arrow = 0 := by
      rw [Category.assoc]
      exact kernel.condition (S.arrow ≫ p)
    let k := kernel.lift (S.arrow ≫ p) (Subobject.ofLE M S hMS) hcondition
    let l := Abelian.monoLift M.arrow
      (kernel.ι (S.arrow ≫ p) ≫ S.arrow) hkernelCondition
    have hk : k ≫ kernel.ι (S.arrow ≫ p) = Subobject.ofLE M S hMS :=
      kernel.lift_ι _ _ _
    have hl : l ≫ M.arrow = kernel.ι (S.arrow ≫ p) ≫ S.arrow :=
      Abelian.monoLift_comp _ _ _
    have hkl : k ≫ l = 𝟙 _ := by
      apply (cancel_mono M.arrow).mp
      rw [Category.assoc, hl, ← Category.assoc, hk, Subobject.ofLE_arrow,
        Category.id_comp]
    have hlk : l ≫ k = 𝟙 _ := by
      apply (cancel_mono (kernel.ι (S.arrow ≫ p))).mp
      rw [Category.assoc, hk, Category.id_comp]
      apply (cancel_mono S.arrow).mp
      rw [Category.assoc, Subobject.ofLE_arrow, hl]
    have hchargeKernel : Z.charge (M : A) = Z.charge (kernel (S.arrow ≫ p)) :=
      Z.charge_eq_of_iso ⟨k, l, hkl, hlk⟩
    have hchargeCoimage := Z.charge_eq_of_iso (Abelian.coimageIsoImage' (S.arrow ≫ p))
    have hchargeImage := Z.charge_eq_of_iso (imageSubobjectIso (S.arrow ≫ p))
    rw [← hchargeKernel] at hses
    exact (hchargeImage.trans hchargeCoimage.symm).trans
      (add_left_cancel (hses.symm.trans hS))
  have hcharge : Z.charge (pbI : A) = Z.charge (S : A) := by
    rw [hpb, hI]
    exact hS.symm
  rcases hle.eq_or_lt with heq | hlt
  · exact heq.symm
  · exfalso
    have hshort := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_cokernel (Subobject.ofLE S pbI hle))
      inferInstance inferInstance
    have hadd := Z.additive _ hshort
    have hcokernel :
        Z.charge (cokernel (Subobject.ofLE S pbI hle)) = 0 := by
      have h : Z.charge (S : A) + 0 = Z.charge (S : A) +
          Z.charge (cokernel (Subobject.ofLE S pbI hle)) := by
        rw [add_zero]
        exact hcharge.symm.trans hadd
      exact (add_left_cancel h).symm
    have hnonzero : ¬IsZero (cokernel (Subobject.ofLE S pbI hle)) := by
      intro hzero
      haveI : Epi (Subobject.ofLE S pbI hle) :=
        Preadditive.epi_of_isZero_cokernel _ hzero
      haveI : IsIso (Subobject.ofLE S pbI hle) := isIso_of_mono_of_epi _
      exact (ne_of_lt hlt) (Subobject.eq_of_comm (asIso (Subobject.ofLE S pbI hle))
        (Subobject.ofLE_arrow hle))
    exact semiClosedUpperHalfPlane_ne_zero
      (Z.nonzero_mem _ hnonzero) hcokernel

/-- Consecutive pulled-back quotient subobjects have the same charge as the
corresponding quotient factor. -/
theorem charge_cokernel_pullback_eq (Z : StabilityFunction A) {E : A}
    (M : Subobject E) {B₁ B₂ : Subobject (cokernel M.arrow)} (h : B₁ ≤ B₂) :
    Z.charge (cokernel (Subobject.ofLE
      ((Subobject.pullback (cokernel.π M.arrow)).obj B₁)
      ((Subobject.pullback (cokernel.π M.arrow)).obj B₂)
      (Functor.monotone _ h))) =
      Z.charge (cokernel (Subobject.ofLE B₁ B₂ h)) := by
  let pbB₁ := (Subobject.pullback (cokernel.π M.arrow)).obj B₁
  let pbB₂ := (Subobject.pullback (cokernel.π M.arrow)).obj B₂
  let hpull : pbB₁ ≤ pbB₂ := Functor.monotone _ h
  have hshort₁ := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_cokernel (Subobject.ofLE pbB₁ pbB₂ hpull))
    inferInstance inferInstance
  have hshort₂ := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_cokernel (Subobject.ofLE B₁ B₂ h))
    inferInstance inferInstance
  have h₁ := Z.additive _ hshort₁
  have h₂ := Z.additive _ hshort₂
  have hB₁ := charge_pullback_eq_add Z M B₁
  have hB₂ := charge_pullback_eq_add Z M B₂
  linear_combination -h₁ + h₂ - hB₁ + hB₂

/-- Consecutive pulled-back quotient subobjects have the same phase as the
corresponding quotient factor. -/
theorem phase_cokernel_pullback_eq (Z : StabilityFunction A) {E : A}
    (M : Subobject E) {B₁ B₂ : Subobject (cokernel M.arrow)} (h : B₁ ≤ B₂) :
    Z.phase (cokernel (Subobject.ofLE
      ((Subobject.pullback (cokernel.π M.arrow)).obj B₁)
      ((Subobject.pullback (cokernel.π M.arrow)).obj B₂)
      (Functor.monotone _ h))) =
      Z.phase (cokernel (Subobject.ofLE B₁ B₂ h)) := by
  simp only [StabilityFunction.phase, charge_cokernel_pullback_eq Z M h]

/-- Consecutive pulled-back quotient factors are canonically isomorphic. -/
noncomputable def cokernelPullbackIso (Z : StabilityFunction A) {E : A}
    (M : Subobject E) {B₁ B₂ : Subobject (cokernel M.arrow)} (h : B₁ < B₂) :
    cokernel (Subobject.ofLE
      ((Subobject.pullback (cokernel.π M.arrow)).obj B₁)
      ((Subobject.pullback (cokernel.π M.arrow)).obj B₂)
      (Functor.monotone _ h.le)) ≅
      cokernel (Subobject.ofLE B₁ B₂ h.le) := by
  let p := cokernel.π M.arrow
  let pbB₁ := (Subobject.pullback p).obj B₁
  let pbB₂ := (Subobject.pullback p).obj B₂
  let hpull : pbB₁ ≤ pbB₂ := Functor.monotone _ h.le
  have hw₁ := (Subobject.isPullback p B₁).w
  have hw₂ := (Subobject.isPullback p B₂).w
  have hcomm : Subobject.ofLE pbB₁ pbB₂ hpull ≫
      Subobject.pullbackπ p B₂ =
      Subobject.pullbackπ p B₁ ≫ Subobject.ofLE B₁ B₂ h.le := by
    apply (cancel_mono B₂.arrow).mp
    simp only [Category.assoc, Subobject.ofLE_arrow]
    calc
      Subobject.ofLE pbB₁ pbB₂ hpull ≫
          (Subobject.pullbackπ p B₂ ≫ B₂.arrow) =
          Subobject.ofLE pbB₁ pbB₂ hpull ≫ (pbB₂.arrow ≫ p) := by rw [hw₂]
      _ = (Subobject.ofLE pbB₁ pbB₂ hpull ≫ pbB₂.arrow) ≫ p := by
        rw [Category.assoc]
      _ = pbB₁.arrow ≫ p := by rw [Subobject.ofLE_arrow]
      _ = Subobject.pullbackπ p B₁ ≫ B₁.arrow := hw₁.symm
  have hfactor : Subobject.ofLE pbB₁ pbB₂ hpull ≫
      (Subobject.pullbackπ p B₂ ≫ cokernel.π (Subobject.ofLE B₁ B₂ h.le)) = 0 := by
    rw [← Category.assoc, hcomm, Category.assoc, cokernel.condition, comp_zero]
  let f := cokernel.desc (Subobject.ofLE pbB₁ pbB₂ hpull)
    (Subobject.pullbackπ p B₂ ≫ cokernel.π (Subobject.ofLE B₁ B₂ h.le)) hfactor
  haveI : Epi (Subobject.pullbackπ p B₂) := by
    rw [← (Subobject.isPullback p B₂).isoPullback_hom_fst]
    infer_instance
  haveI : Epi f := epi_of_epi_fac (cokernel.π_desc _ _ _)
  haveI : Mono f := by
    suffices hk : kernel.ι f = 0 from Preadditive.mono_of_kernel_zero hk
    have hshort := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_kernel f) inferInstance inferInstance
    have hadd := Z.additive _ hshort
    have hcharge : Z.charge (cokernel (Subobject.ofLE pbB₁ pbB₂ hpull)) =
        Z.charge (cokernel (Subobject.ofLE B₁ B₂ h.le)) :=
      charge_cokernel_pullback_eq Z M h.le
    rw [hcharge] at hadd
    have hkernelCharge : Z.charge (kernel f) = 0 :=
      add_eq_right.mp hadd.symm
    by_contra hk
    have hkernel : ¬IsZero (kernel f) := fun hzero =>
      hk (zero_of_source_iso_zero _ hzero.isoZero)
    exact semiClosedUpperHalfPlane_ne_zero
      (Z.nonzero_mem _ hkernel) hkernelCharge
  haveI : IsIso f := isIso_of_mono_of_epi f
  exact asIso f

/-- A semistable object of phase above an HN factor has no morphisms to that
factor. -/
theorem hom_eq_zero_to_factor {Z : StabilityFunction A} {E B : A}
    (F : AbelianHNFiltration Z E) (hB : Z.IsSemistable B)
    (j : Fin F.n) (hphase : F.phase j < Z.phase B)
    (f : B ⟶ cokernel (Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
      (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)))) : f = 0 :=
  Z.hom_eq_zero_of_semistable_phase_gt hB (F.factor_semistable j)
    (F.factor_phase j ▸ hphase) f

/-- A semistable subobject whose phase is above every factor from index `k`
onward lies in the `k`-th term of an HN filtration. -/
theorem le_chain_of_semistable_phase_gt {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) {B : Subobject E}
    (hB : Z.IsSemistable (B : A)) {k : ℕ} (hk : k ≤ F.n)
    (hphase : ∀ j : Fin F.n, k ≤ j.val →
      F.phase j < Z.phase (B : A)) :
    B ≤ F.chain ⟨k, by lia⟩ := by
  suffices descend : ∀ d m (hm : m < F.n + 1), F.n - m = d → k ≤ m →
      B ≤ F.chain ⟨m, hm⟩ from
    descend (F.n - k) k (by lia) rfl le_rfl
  intro d
  induction d with
  | zero =>
      intro m hm hd _
      have hmn : m = F.n := by lia
      subst hmn
      rw [F.chain_top]
      exact le_top
  | succ d ih =>
      intro m hm hd hkm
      have hnext : B ≤ F.chain ⟨m + 1, by lia⟩ :=
        ih (m + 1) (by lia) (by lia) (by lia)
      let j : Fin F.n := ⟨m, by lia⟩
      have hsucc : (j.succ : Fin (F.n + 1)) = ⟨m + 1, by lia⟩ :=
        Fin.ext (by simp [j])
      have hBnext : B ≤ F.chain j.succ := hsucc ▸ hnext
      have hzero : Subobject.ofLE B (F.chain j.succ) hBnext ≫
          cokernel.π (Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
            (le_of_lt (F.chain_strictMono j.castSucc_lt_succ))) = 0 :=
        F.hom_eq_zero_to_factor hB j (hphase j (by simp [j]; lia)) _
      exact le_of_ofLE_comp_cokernel_zero hBnext
        (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)) hzero

/-- A semistable subobject whose phase is above the highest HN phase is zero. -/
theorem eq_bot_of_semistable_phase_gt_phiPlus {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) {B : Subobject E}
    (hB : Z.IsSemistable (B : A))
    (hphase : F.phiPlus < Z.phase (B : A)) : B = ⊥ := by
  apply le_bot_iff.mp
  rw [← F.chain_bot]
  apply F.le_chain_of_semistable_phase_gt hB (Nat.zero_le _)
  intro j _
  exact lt_of_le_of_lt
    (F.phase_strictAnti.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))) hphase

/-- The first nonzero term in an HN filtration is not bottom. -/
theorem chain_one_ne_bot {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) :
    F.chain ⟨1, by have := F.nonempty; lia⟩ ≠ ⊥ := by
  have hn := F.nonempty
  intro heq
  have hlt : F.chain ⟨0, by lia⟩ < F.chain ⟨1, by lia⟩ :=
    F.chain_strictMono (Fin.mk_lt_mk.mpr (by lia))
  rw [F.chain_bot, heq] at hlt
  exact lt_irrefl _ hlt

/-- The phase of the first nonzero term is the highest HN phase. -/
theorem phase_chain_one {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) :
    Z.phase (F.chain ⟨1, by have := F.nonempty; lia⟩ : A) = F.phiPlus := by
  have hn := F.nonempty
  change Z.phase (F.chain ⟨1, by lia⟩ : A) = F.phase ⟨0, F.nonempty⟩
  rw [← F.factor_phase ⟨0, F.nonempty⟩]
  have hzero : F.chain (⟨0, F.nonempty⟩ : Fin F.n).castSucc = ⊥ := by
    change F.chain ⟨0, by lia⟩ = ⊥
    exact F.chain_bot
  exact ((Z.phase_cokernel_ofLE_congr hzero rfl).trans
    (Z.phase_eq_of_iso
      (StabilityFunction.subobjectCokernelBotIso
        (F.chain ⟨1, by lia⟩) bot_le))).symm

/-- The first nonzero term in an HN filtration is semistable. -/
theorem chain_one_isSemistable {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) :
    Z.IsSemistable (F.chain ⟨1, by have := F.nonempty; lia⟩ : A) := by
  have hn := F.nonempty
  have hzero : F.chain (⟨0, F.nonempty⟩ : Fin F.n).castSucc = ⊥ := by
    change F.chain ⟨0, by lia⟩ = ⊥
    exact F.chain_bot
  have hfactor : Z.IsSemistable
      (cokernel (Subobject.ofLE (F.chain
        (⟨0, F.nonempty⟩ : Fin F.n).castSucc)
        (F.chain (⟨0, F.nonempty⟩ : Fin F.n).succ)
        (le_of_lt (F.chain_strictMono
          (⟨0, F.nonempty⟩ : Fin F.n).castSucc_lt_succ)))) :=
    F.factor_semistable ⟨0, F.nonempty⟩
  have hnormalized : Z.IsSemistable
      (cokernel (Subobject.ofLE (⊥ : Subobject E)
        (F.chain ⟨1, by lia⟩) bot_le)) :=
    Z.isSemistable_cokernel_ofLE_congr hzero.symm rfl hfactor
  exact Z.isSemistable_of_iso
    (StabilityFunction.subobjectCokernelBotIso
      (F.chain ⟨1, by lia⟩) bot_le) hnormalized

/-- The highest phase is intrinsic: any two owner HN filtrations of the same
object have the same first phase. -/
theorem phiPlus_eq {Z : StabilityFunction A} {E : A}
    (F G : AbelianHNFiltration Z E) : F.phiPlus = G.phiPlus := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hGF
    have hbot := G.eq_bot_of_semistable_phase_gt_phiPlus
      F.chain_one_isSemistable (F.phase_chain_one ▸ hGF)
    exact F.chain_one_ne_bot hbot
  · apply le_of_not_gt
    intro hFG
    have hbot := F.eq_bot_of_semistable_phase_gt_phiPlus
      G.chain_one_isSemistable (G.phase_chain_one ▸ hFG)
    exact G.chain_one_ne_bot hbot

/-- The first nonzero term is intrinsic: any two owner HN filtrations of the
same object have the same maximally destabilizing subobject. -/
theorem chain_one_eq {Z : StabilityFunction A} {E : A}
    (F G : AbelianHNFiltration Z E) :
    F.chain ⟨1, by have := F.nonempty; lia⟩ =
      G.chain ⟨1, by have := G.nonempty; lia⟩ := by
  apply le_antisymm
  · apply G.le_chain_of_semistable_phase_gt F.chain_one_isSemistable G.nonempty
    intro j hj
    calc
      G.phase j < G.phiPlus :=
        G.phase_strictAnti (Fin.mk_lt_mk.mpr (by lia))
      _ = F.phiPlus := (F.phiPlus_eq G).symm
      _ = Z.phase (F.chain ⟨1, by have := F.nonempty; lia⟩ : A) :=
        F.phase_chain_one.symm
  · apply F.le_chain_of_semistable_phase_gt G.chain_one_isSemistable F.nonempty
    intro j hj
    calc
      F.phase j < F.phiPlus :=
        F.phase_strictAnti (Fin.mk_lt_mk.mpr (by lia))
      _ = G.phiPlus := F.phiPlus_eq G
      _ = Z.phase (G.chain ⟨1, by have := G.nonempty; lia⟩ : A) :=
        G.phase_chain_one.symm

/-- No nonzero semistable subobject has phase above the first HN phase. -/
theorem semistable_phase_le_phiPlus {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) {B : Subobject E}
    (hB : Z.IsSemistable (B : A)) : Z.phase (B : A) ≤ F.phiPlus := by
  apply le_of_not_gt
  intro hphase
  have hbot := F.eq_bot_of_semistable_phase_gt_phiPlus hB hphase
  exact hB.1 ((StabilityFunction.subobject_isZero_iff_eq_bot B).2 hbot)

/-- A semistable subobject at the highest HN phase is contained in the
intrinsic first HN term. -/
theorem le_chain_one_of_semistable_phase_eq_phiPlus
    {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) {B : Subobject E}
    (hB : Z.IsSemistable (B : A))
    (hphase : Z.phase (B : A) = F.phiPlus) :
    B ≤ F.chain ⟨1, by have := F.nonempty; lia⟩ := by
  apply F.le_chain_of_semistable_phase_gt hB F.nonempty
  intro j hj
  calc
    F.phase j < F.phiPlus :=
      F.phase_strictAnti (Fin.mk_lt_mk.mpr (by lia))
    _ = Z.phase (B : A) := hphase.symm

/-- The first HN term contains every semistable subobject having the highest
HN phase. -/
theorem chain_one_maximal_semistable_phase {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) {B : Subobject E}
    (hB : Z.IsSemistable (B : A))
    (hphase : Z.phase (B : A) = F.phiPlus) :
    B ≤ F.chain ⟨1, by have := F.nonempty; lia⟩ :=
  F.le_chain_one_of_semistable_phase_eq_phiPlus hB hphase

/-- Every morphism from an HN-filtered object to a semistable object whose
phase is below the lowest HN phase is zero. -/
theorem hom_eq_zero_to_semistable_of_phase_lt_phiMinus
    {Z : StabilityFunction A} {E B : A} (F : AbelianHNFiltration Z E)
    (hB : Z.IsSemistable B) (hphase : Z.phase B < F.phiMinus)
    (f : E ⟶ B) : f = 0 := by
  have hrestrict : ∀ m : ℕ, (hm : m ≤ F.n) →
      (F.chain ⟨m, by lia⟩).arrow ≫ f = 0 := by
    intro m
    induction m with
    | zero =>
        intro _
        rw [F.chain_bot]
        simp
    | succ m ih =>
        intro hm
        let j : Fin F.n := ⟨m, by lia⟩
        have hprevious : (F.chain j.castSucc).arrow ≫ f = 0 := by
          change (F.chain ⟨m, by lia⟩).arrow ≫ f = 0
          exact ih (by lia)
        have hcomp : Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
              (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)) ≫
            ((F.chain j.succ).arrow ≫ f) = 0 := by
          calc
            Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
                  (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)) ≫
                ((F.chain j.succ).arrow ≫ f) =
                (F.chain j.castSucc).arrow ≫ f := by
              rw [← Category.assoc, Subobject.ofLE_arrow]
            _ = 0 := hprevious
        let descended := cokernel.desc
          (Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
            (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)))
          ((F.chain j.succ).arrow ≫ f) hcomp
        have hfactor_phase : Z.phase B <
            Z.phase (cokernel (Subobject.ofLE (F.chain j.castSucc)
              (F.chain j.succ)
              (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)))) := by
          rw [F.factor_phase j]
          exact lt_of_lt_of_le hphase (F.phase_mem_range j).1
        have hdescended : descended = 0 :=
          Z.hom_eq_zero_of_semistable_phase_gt (F.factor_semistable j) hB
            hfactor_phase descended
        change (F.chain j.succ).arrow ≫ f = 0
        calc
          (F.chain j.succ).arrow ≫ f =
              cokernel.π (Subobject.ofLE (F.chain j.castSucc)
                (F.chain j.succ)
                (le_of_lt (F.chain_strictMono j.castSucc_lt_succ))) ≫
                descended := (cokernel.π_desc _ _ _).symm
          _ = 0 := by rw [hdescended, comp_zero]
  have htop : (⊤ : Subobject E).arrow ≫ f = 0 := by
    rw [← F.chain_top]
    exact hrestrict F.n le_rfl
  apply (cancel_epi (⊤ : Subobject E).arrow).mp
  simpa using htop

/-- The lowest phase is intrinsic: any two owner HN filtrations of the same
object have the same last phase. -/
theorem phiMinus_eq {Z : StabilityFunction A} {E : A}
    (F G : AbelianHNFiltration Z E) : F.phiMinus = G.phiMinus := by
  have no_strict_order : ∀ (H K : AbelianHNFiltration Z E),
      ¬H.phiMinus < K.phiMinus := by
    intro H K hHK
    have hn := H.nonempty
    let last : Fin H.n := ⟨H.n - 1, by have := H.nonempty; lia⟩
    have hlast : H.chain last.succ = ⊤ := by
      have hindex : last.succ = ⟨H.n, by lia⟩ :=
        Fin.ext (by simp [last]; lia)
      rw [hindex, H.chain_top]
    haveI : IsIso (H.chain last.succ).arrow := by
      rw [hlast]
      infer_instance
    let q : E ⟶ cokernel (Subobject.ofLE (H.chain last.castSucc)
        (H.chain last.succ)
        (le_of_lt (H.chain_strictMono last.castSucc_lt_succ))) :=
      inv (H.chain last.succ).arrow ≫
        cokernel.π (Subobject.ofLE (H.chain last.castSucc)
          (H.chain last.succ)
          (le_of_lt (H.chain_strictMono last.castSucc_lt_succ)))
    haveI : Epi q := inferInstance
    have hq : q = 0 := K.hom_eq_zero_to_semistable_of_phase_lt_phiMinus
      (H.factor_semistable last) (by
        rw [H.factor_phase last]
        exact hHK) q
    exact (H.factor_semistable last).1 (IsZero.of_epi_eq_zero q hq)
  exact le_antisymm (le_of_not_gt (no_strict_order G F))
    (le_of_not_gt (no_strict_order F G))

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

namespace StabilityFunction

/-- The canonical maximally destabilizing subobject of a nonzero object. -/
noncomputable def maxDestabilizingSubobject (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) : Subobject E :=
  let F := Classical.choice (hHN E hE)
  F.chain ⟨1, by have := F.nonempty; lia⟩

/-- The canonical maximally destabilizing subobject agrees with the first
nonzero term of every owner HN filtration. -/
theorem maxDestabilizingSubobject_eq_filtration (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) {E : A} (hE : ¬IsZero E)
    (F : AbelianHNFiltration Z E) :
    Z.maxDestabilizingSubobject hHN E hE =
      F.chain ⟨1, by have := F.nonempty; lia⟩ :=
  (Classical.choice (hHN E hE)).chain_one_eq F

/-- The canonical maximally destabilizing subobject is nonzero. -/
theorem maxDestabilizingSubobject_ne_bot (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) :
    Z.maxDestabilizingSubobject hHN E hE ≠ ⊥ :=
  (Classical.choice (hHN E hE)).chain_one_ne_bot

/-- The canonical maximally destabilizing subobject is semistable. -/
theorem maxDestabilizingSubobject_isSemistable (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) :
    Z.IsSemistable (Z.maxDestabilizingSubobject hHN E hE : A) :=
  (Classical.choice (hHN E hE)).chain_one_isSemistable

/-- A nonzero object is semistable exactly when its canonical maximally
destabilizing subobject is the whole object. -/
theorem maxDestabilizingSubobject_eq_top_iff_isSemistable
    (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) :
    Z.maxDestabilizingSubobject hHN E hE = ⊤ ↔ Z.IsSemistable E := by
  let F := Classical.choice (hHN E hE)
  rw [Z.maxDestabilizingSubobject_eq_filtration hHN hE F]
  constructor
  · intro htop
    have htopsemistable : Z.IsSemistable ((⊤ : Subobject E) : A) :=
      htop ▸ F.chain_one_isSemistable
    exact Z.isSemistable_of_iso (asIso (⊤ : Subobject E).arrow)
      htopsemistable
  · intro hEsemistable
    have hn : F.n = 1 := F.n_eq_one_of_semistable hEsemistable
    have hindex : (⟨1, by have := F.nonempty; lia⟩ : Fin (F.n + 1)) =
        ⟨F.n, by lia⟩ := Fin.ext (by lia)
    rw [hindex, F.chain_top]

/-- The quotient left after removing the canonical maximally destabilizing
subobject. -/
noncomputable def destabilizingQuotient (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) : A :=
  cokernel (Z.maxDestabilizingSubobject hHN E hE).arrow

/-- The destabilizing quotient is zero exactly for semistable objects. -/
theorem isZero_destabilizingQuotient_iff_isSemistable
    (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) :
    IsZero (Z.destabilizingQuotient hHN E hE) ↔ Z.IsSemistable E := by
  rw [← Z.maxDestabilizingSubobject_eq_top_iff_isSemistable hHN E hE]
  constructor
  · intro hquotient
    haveI : Epi (Z.maxDestabilizingSubobject hHN E hE).arrow :=
      Preadditive.epi_of_isZero_cokernel _ hquotient
    haveI : IsIso (Z.maxDestabilizingSubobject hHN E hE).arrow :=
      isIso_of_mono_of_epi _
    exact Subobject.eq_top_of_isIso_arrow _
  · intro htop
    change IsZero (cokernel (Z.maxDestabilizingSubobject hHN E hE).arrow)
    rw [htop]
    exact isZero_cokernel_of_epi (⊤ : Subobject E).arrow

/-- A non-semistable object has a nonzero destabilizing quotient. -/
theorem destabilizingQuotient_not_isZero_of_not_isSemistable
    (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) (hnot : ¬Z.IsSemistable E) :
    ¬IsZero (Z.destabilizingQuotient hHN E hE) :=
  fun hzero => hnot ((Z.isZero_destabilizingQuotient_iff_isSemistable
    hHN E hE).1 hzero)

/-- The canonical short complex presenting an object as an extension of its
maximally destabilizing subobject by the destabilizing quotient. -/
noncomputable def destabilizingShortComplex (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) : ShortComplex A :=
  ShortComplex.mk (Z.maxDestabilizingSubobject hHN E hE).arrow
    (cokernel.π (Z.maxDestabilizingSubobject hHN E hE).arrow)
    (cokernel.condition (Z.maxDestabilizingSubobject hHN E hE).arrow)

/-- The canonical destabilizing short complex is short exact. -/
theorem destabilizingShortComplex_shortExact (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) :
    (Z.destabilizingShortComplex hHN E hE).ShortExact := by
  change (ShortComplex.mk _ _ _).ShortExact
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_cokernel
      (Z.maxDestabilizingSubobject hHN E hE).arrow)
    inferInstance inferInstance

/-- The central charge splits across the canonical destabilizing short exact
sequence. -/
theorem charge_eq_maxDestabilizingSubobject_add_destabilizingQuotient
    (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) :
    Z.charge E = Z.charge (Z.maxDestabilizingSubobject hHN E hE : A) +
      Z.charge (Z.destabilizingQuotient hHN E hE) :=
  Z.additive (Z.destabilizingShortComplex hHN E hE)
    (Z.destabilizingShortComplex_shortExact hHN E hE)

/-- The intrinsic highest HN phase of a nonzero object. -/
noncomputable def phiPlus (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) : ℝ :=
  (Classical.choice (hHN E hE)).phiPlus

/-- The intrinsic lowest HN phase of a nonzero object. -/
noncomputable def phiMinus (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) : ℝ :=
  (Classical.choice (hHN E hE)).phiMinus

/-- The intrinsic highest phase agrees with every owner HN filtration. -/
theorem phiPlus_eq_filtration (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    {E : A} (hE : ¬IsZero E) (F : AbelianHNFiltration Z E) :
    Z.phiPlus hHN E hE = F.phiPlus :=
  (Classical.choice (hHN E hE)).phiPlus_eq F

/-- The canonical maximally destabilizing subobject has the intrinsic highest
HN phase. -/
theorem phase_maxDestabilizingSubobject (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) :
    Z.phase (Z.maxDestabilizingSubobject hHN E hE : A) =
      Z.phiPlus hHN E hE :=
  (Classical.choice (hHN E hE)).phase_chain_one

/-- Every semistable subobject at the intrinsic highest HN phase lies in the
canonical maximally destabilizing subobject. -/
theorem le_maxDestabilizingSubobject_of_semistable_phase_eq_phiPlus
    (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    {E : A} (hE : ¬IsZero E) {B : Subobject E}
    (hB : Z.IsSemistable (B : A))
    (hphase : Z.phase (B : A) = Z.phiPlus hHN E hE) :
    B ≤ Z.maxDestabilizingSubobject hHN E hE := by
  let F := Classical.choice (hHN E hE)
  rw [Z.phiPlus_eq_filtration hHN hE F] at hphase
  rw [Z.maxDestabilizingSubobject_eq_filtration hHN hE F]
  exact F.le_chain_one_of_semistable_phase_eq_phiPlus hB hphase

/-- The intrinsic lowest phase agrees with every owner HN filtration. -/
theorem phiMinus_eq_filtration (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    {E : A} (hE : ¬IsZero E) (F : AbelianHNFiltration Z E) :
    Z.phiMinus hHN E hE = F.phiMinus :=
  (Classical.choice (hHN E hE)).phiMinus_eq F

/-- The intrinsic lowest HN phase is at most the intrinsic highest phase. -/
theorem phiMinus_le_phiPlus (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) :
    Z.phiMinus hHN E hE ≤ Z.phiPlus hHN E hE := by
  let F := Classical.choice (hHN E hE)
  rw [Z.phiMinus_eq_filtration hHN hE F,
    Z.phiPlus_eq_filtration hHN hE F]
  exact F.phiMinus_le_phiPlus

/-- A nonzero object is semistable exactly when its intrinsic HN phase
interval degenerates to a point. -/
theorem isSemistable_iff_phiPlus_eq_phiMinus (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) :
    Z.IsSemistable E ↔ Z.phiPlus hHN E hE = Z.phiMinus hHN E hE := by
  let F := Classical.choice (hHN E hE)
  rw [Z.phiPlus_eq_filtration hHN hE F,
    Z.phiMinus_eq_filtration hHN hE F]
  constructor
  · intro hsemistable
    have hn : F.n = 1 := F.n_eq_one_of_semistable hsemistable
    apply congrArg F.phase
    apply Fin.ext
    lia
  · intro hextrema
    apply F.isSemistable_of_n_eq_one
    by_contra hn
    have hn_gt : 1 < F.n := by
      have := F.nonempty
      lia
    have hlast_lt : F.phiMinus < F.phiPlus := by
      exact F.phase_strictAnti (Fin.mk_lt_mk.mpr (by lia))
    exact (ne_of_lt hlast_lt) hextrema.symm

end StabilityFunction

end CategoryTheory.Triangulated
