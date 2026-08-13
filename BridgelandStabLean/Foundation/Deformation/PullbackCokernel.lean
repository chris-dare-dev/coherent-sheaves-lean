/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.Deformation.FirstStrictSES
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Pullback and cokernel transport in an owner thin interval

Strict subobjects of a strict quotient pull back to strict subobjects.  Their
cokernels agree up to isomorphism, so the perturbed charge and phase transport
across the pullback square.  These are the categorical and phase-theoretic
inputs for strict maximal destabilizing quotient selection.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

namespace BridgelandStabLean.Foundation.Deformation

open BridgelandStabLean.Foundation
open BridgelandStabLean.ForMathlib.CategoryTheory

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

namespace Slicing.IntervalCat

variable {s : Slicing C} {a b : ℝ}
variable [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- Pulling back a strict epimorphism along an interval subobject preserves
strict epimorphy of the pullback projection. -/
theorem pullbackProjection_strictEpi {X Y : s.IntervalCat C a b}
    (p : X ⟶ Y) (hp : IsStrictEpi p) (B : Subobject Y) :
    IsStrictEpi (Subobject.pullbackπ p B) := by
  let e := (Subobject.isPullback p B).isoPullback
  have hpb : IsStrictEpi (pullback.fst B.arrow p) :=
    QuasiAbelian.pullback_strictEpi B.arrow p hp
  have he : e.hom ≫ pullback.fst B.arrow p = Subobject.pullbackπ p B :=
    (Subobject.isPullback p B).isoPullback_hom_fst
  have hcomp : IsStrictEpi (e.hom ≫ pullback.fst B.arrow p) :=
    BridgelandStabLean.Foundation.Slicing.IntervalCat.comp_strictEpi C s
      e.hom (pullback.fst B.arrow p) isStrictEpi_of_isIso hpb
  simpa [he] using hcomp

/-- Pulling back a strict interval subobject preserves strictness of its
canonical arrow. -/
theorem pullbackArrow_strictMono {X Y : s.IntervalCat C a b}
    (p : X ⟶ Y) (B : Subobject Y) (hB : IsStrictMono B.arrow) :
    IsStrictMono (((Subobject.pullback p).obj B).arrow) := by
  let pb := (Subobject.pullback p).obj B
  let sq := Subobject.isPullback p B
  let hKerB := hB.isLimitKernelFork
  letI : NormalMono pb.arrow :=
    { Z := cokernel B.arrow
      g := p ≫ cokernel.π B.arrow
      w := by
        calc
          pb.arrow ≫ (p ≫ cokernel.π B.arrow) =
              (pb.arrow ≫ p) ≫ cokernel.π B.arrow := by simp
          _ = (Subobject.pullbackπ p B ≫ B.arrow) ≫
              cokernel.π B.arrow := by rw [sq.w]
          _ = 0 := by simp
      isLimit := KernelFork.IsLimit.ofι' pb.arrow
        (by
          calc
            pb.arrow ≫ (p ≫ cokernel.π B.arrow) =
                (pb.arrow ≫ p) ≫ cokernel.π B.arrow := by simp
            _ = (Subobject.pullbackπ p B ≫ B.arrow) ≫
                cokernel.π B.arrow := by rw [sq.w]
            _ = 0 := by simp)
        (fun {W} g hg => by
          let u : W ⟶ (B : s.IntervalCat C a b) :=
            hKerB.lift (KernelFork.ofι (g ≫ p) (by
              rw [Category.assoc]
              exact hg))
          have hu : u ≫ B.arrow = g ≫ p :=
            hKerB.fac _ WalkingParallelPair.zero
          exact ⟨sq.lift u g hu, sq.lift_snd u g hu⟩) }
  exact isStrictMono_of_normalMono

/-- A kernel subobject lies below the pullback of every subobject of its
canonical cokernel. -/
theorem le_pullbackCokernel {X : s.IntervalCat C a b} (M : Subobject X)
    (B : Subobject (cokernel M.arrow)) :
    M ≤ (Subobject.pullback (cokernel.π M.arrow)).obj B := by
  let q := cokernel.π M.arrow
  let sq := Subobject.isPullback q B
  refine Subobject.le_of_comm (sq.lift 0 M.arrow (by
    rw [zero_comp]
    exact (cokernel.condition M.arrow).symm)) ?_
  exact sq.lift_snd 0 M.arrow (by
    rw [zero_comp]
    exact (cokernel.condition M.arrow).symm)

/-- The inclusion of a kernel subobject into a cokernel pullback is killed by
the pullback projection. -/
theorem ofLE_pullbackProjection_eq_zero {X : s.IntervalCat C a b}
    (M : Subobject X) (B : Subobject (cokernel M.arrow)) :
    Subobject.ofLE M _ (le_pullbackCokernel C M B) ≫
      Subobject.pullbackπ (cokernel.π M.arrow) B = 0 := by
  let q := cokernel.π M.arrow
  let pbB := (Subobject.pullback q).obj B
  let hle := le_pullbackCokernel C M B
  let sq := Subobject.isPullback q B
  apply (cancel_mono B.arrow).1
  calc
    (Subobject.ofLE M pbB hle ≫ Subobject.pullbackπ q B) ≫ B.arrow =
        Subobject.ofLE M pbB hle ≫ (pbB.arrow ≫ q) := by
          rw [Category.assoc, sq.w]
    _ = M.arrow ≫ q := by simp
    _ = 0 := cokernel.condition M.arrow
    _ = 0 ≫ B.arrow := by simp

/-- A nonzero subobject of a cokernel pulls back to a strict enlargement of
the kernel subobject. -/
theorem lt_pullbackCokernel_of_ne_bot {X : s.IntervalCat C a b}
    {M : Subobject X} {B : Subobject (cokernel M.arrow)} (hB : B ≠ ⊥) :
    M < (Subobject.pullback (cokernel.π M.arrow)).obj B := by
  let q := cokernel.π M.arrow
  let pbB := (Subobject.pullback q).obj B
  have hle : M ≤ pbB := le_pullbackCokernel C M B
  refine lt_of_le_of_ne hle ?_
  intro hEq
  let heqObj : Subobject.underlying.obj M = Subobject.underlying.obj pbB :=
    congrArg Subobject.underlying.obj hEq
  have hi : Subobject.ofLE M pbB hle = eqToHom heqObj := by
    apply (cancel_mono pbB.arrow).1
    calc
      Subobject.ofLE M pbB hle ≫ pbB.arrow = M.arrow :=
        Subobject.ofLE_arrow hle
      _ = eqToHom heqObj ≫ pbB.arrow :=
        (Subobject.arrow_congr M pbB hEq).symm
  have hzero : Subobject.pullbackπ q B = 0 := by
    have hcomp := ofLE_pullbackProjection_eq_zero C M B
    rw [hi] at hcomp
    letI : Epi (eqToHom heqObj) := by infer_instance
    exact (cancel_epi (eqToHom heqObj)).1 (by simpa using hcomp)
  have hπ : IsStrictEpi (Subobject.pullbackπ q B) :=
    pullbackProjection_strictEpi C q (isStrictEpi_cokernel M.arrow) B
  haveI : Epi (Subobject.pullbackπ q B) := hπ.epi
  have hBZ : IsZero (B : s.IntervalCat C a b) :=
    (IsZero.iff_id_eq_zero _).2 <|
      (cancel_epi (Subobject.pullbackπ q B)).1 (by rw [hzero]; simp)
  exact hB ((subobject_isZero_iff_eq_bot C B).1 hBZ)

/-- A strict proper subobject of a cokernel cannot pull back to the top
subobject. -/
theorem pullbackCokernel_ne_top {X : s.IntervalCat C a b}
    {M : Subobject X} {B : Subobject (cokernel M.arrow)}
    (hB : B ≠ ⊤) (hBstrict : IsStrictMono B.arrow) :
    (Subobject.pullback (cokernel.π M.arrow)).obj B ≠ ⊤ := by
  let q := cokernel.π M.arrow
  let pbB := (Subobject.pullback q).obj B
  intro hpb
  haveI : IsIso pbB.arrow := by
    let heqObj : Subobject.underlying.obj pbB =
        Subobject.underlying.obj (⊤ : Subobject X) :=
      congrArg Subobject.underlying.obj hpb
    have harr : pbB.arrow = eqToHom heqObj ≫ (⊤ : Subobject X).arrow := by
      simpa using (Subobject.arrow_congr pbB ⊤ hpb).symm
    rw [harr]
    infer_instance
  let r : X ⟶ (B : s.IntervalCat C a b) :=
    inv pbB.arrow ≫ Subobject.pullbackπ q B
  have hr : r ≫ B.arrow = q := by
    calc
      r ≫ B.arrow = inv pbB.arrow ≫
          (Subobject.pullbackπ q B ≫ B.arrow) := by simp [r]
      _ = inv pbB.arrow ≫ (pbB.arrow ≫ q) := by
        rw [(Subobject.isPullback q B).w]
      _ = q := by simp
  haveI : Epi q := by infer_instance
  haveI : Epi B.arrow := epi_of_epi_fac hr
  haveI : IsIso B.arrow := hBstrict.isIso
  exact hB (Subobject.eq_top_of_isIso_arrow B)

/-- A strict proper subobject has a nonzero cokernel. -/
theorem cokernel_not_isZero_of_ne_top {X : s.IntervalCat C a b}
    {M : Subobject X} (hM : M ≠ ⊤) (hMstrict : IsStrictMono M.arrow) :
    ¬IsZero (cokernel M.arrow) := by
  intro hZero
  haveI : Epi M.arrow := Preadditive.epi_of_isZero_cokernel M.arrow hZero
  haveI : IsIso M.arrow := hMstrict.isIso
  exact hM (Subobject.eq_top_of_isIso_arrow M)

/-- Pulling back a strict subobject along a cokernel projection preserves its
cokernel object up to canonical isomorphism. -/
def cokernelPullbackIso {X : s.IntervalCat C a b} (M : Subobject X)
    {B : Subobject (cokernel M.arrow)} (hB : IsStrictMono B.arrow) :
    cokernel ((Subobject.pullback (cokernel.π M.arrow)).obj B).arrow ≅
      cokernel B.arrow := by
  let q : X ⟶ cokernel M.arrow := cokernel.π M.arrow
  let pb : Subobject X := (Subobject.pullback q).obj B
  let p : X ⟶ cokernel B.arrow := q ≫ cokernel.π B.arrow
  let hcomp : pb.arrow ≫ p = 0 := by
    calc
      pb.arrow ≫ p = (pb.arrow ≫ q) ≫ cokernel.π B.arrow := by simp [p]
      _ = (Subobject.pullbackπ q B ≫ B.arrow) ≫
          cokernel.π B.arrow := by rw [(Subobject.isPullback q B).w]
      _ = 0 := by simp
  have hKer : IsLimit (KernelFork.ofι pb.arrow hcomp) := by
    refine KernelFork.IsLimit.ofι' pb.arrow hcomp (fun {W} k hk => ?_)
    let u : W ⟶ (B : s.IntervalCat C a b) :=
      hB.isLimitKernelFork.lift (KernelFork.ofι (k ≫ q) (by
        simpa [p, Category.assoc] using hk))
    have hu : u ≫ B.arrow = k ≫ q :=
      hB.isLimitKernelFork.fac _ WalkingParallelPair.zero
    exact ⟨(Subobject.isPullback q B).lift u k hu,
      (Subobject.isPullback q B).lift_snd u k hu⟩
  have hp : IsStrictEpi p :=
    BridgelandStabLean.Foundation.Slicing.IntervalCat.comp_strictEpi C s
      q (cokernel.π B.arrow) (isStrictEpi_cokernel M.arrow)
      (isStrictEpi_cokernel B.arrow)
  let eK' : kernel p ≅ (pb : s.IntervalCat C a b) :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel p) hKer
  let eK : (pb : s.IntervalCat C a b) ≅ kernel p := eK'.symm
  have heK : eK.hom ≫ kernel.ι p = pb.arrow := by
    exact IsLimit.conePointUniqueUpToIso_inv_comp (kernelIsKernel p) hKer
      WalkingParallelPair.zero
  let eC : cokernel pb.arrow ≅ cokernel (kernel.ι p) :=
    cokernel.mapIso pb.arrow (kernel.ι p) eK (Iso.refl _) (by simp [heK])
  let eQ : cokernel (kernel.ι p) ≅ cokernel B.arrow :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (kernel.ι p))
      hp.isColimitCokernelCofork
  exact eC ≪≫ eQ

end Slicing.IntervalCat

namespace SkewedStabilityFunction

variable {σ : StabilityCondition.WithClassMap C κ} {a b : ℝ}
variable {F : SkewedStabilityFunction C κ σ.slicing a b}
variable [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- The perturbed charge of the cokernel is invariant under pullback along a
cokernel projection. -/
theorem charge_cokernelPullback {X : σ.slicing.IntervalCat C a b}
    (M : Subobject X) {B : Subobject (cokernel M.arrow)}
    (hB : IsStrictMono B.arrow) :
    F.charge (cokernel
      ((Subobject.pullback (cokernel.π M.arrow)).obj B).arrow).obj =
      F.charge (cokernel B.arrow).obj := by
  let eC : (cokernel
      ((Subobject.pullback (cokernel.π M.arrow)).obj B).arrow).obj ≅
      (cokernel B.arrow).obj :=
    (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
      (Slicing.IntervalCat.cokernelPullbackIso C M hB)
  exact congrArg F.W (classOf_iso C κ eC)

/-- The perturbed phase of the cokernel is invariant under pullback along a
cokernel projection. -/
theorem phase_cokernelPullback {X : σ.slicing.IntervalCat C a b}
    (M : Subobject X) {B : Subobject (cokernel M.arrow)}
    (hB : IsStrictMono B.arrow) :
    F.phase (cokernel
      ((Subobject.pullback (cokernel.π M.arrow)).obj B).arrow).obj =
      F.phase (cokernel B.arrow).obj := by
  let eC : (cokernel
      ((Subobject.pullback (cokernel.π M.arrow)).obj B).arrow).obj ≅
      (cokernel B.arrow).obj :=
    (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
      (Slicing.IntervalCat.cokernelPullbackIso C M hB)
  exact F.phase_iso eC

/-- In a common phase window of width less than one, the cokernel of an
above-phase proper strict subobject has phase strictly below the original
object. -/
theorem phase_cokernel_lt_of_phase_gt_strictSubobject
    {Y : σ.slicing.IntervalCat C a b} {A : Subobject Y}
    (hAne : A ≠ ⊥) (hAtop : A ≠ ⊤) (hAstrict : IsStrictMono A.arrow)
    (hAphase : F.phase Y.obj <
      F.phase (A : σ.slicing.IntervalCat C a b).obj)
    (hCharge : ∀ {E : C}, σ.slicing.intervalProp C a b E →
      ¬IsZero E → F.ChargeNe E)
    {L U : ℝ}
    (hWindow : ∀ Z : σ.slicing.IntervalCat C a b, ¬IsZero Z.obj →
      L < F.phase Z.obj ∧ F.phase Z.obj < U)
    (hWidth : U - L < 1) :
    F.phase (cokernel A.arrow).obj < F.phase Y.obj := by
  let ψY := F.phase Y.obj
  have hAI : ¬IsZero (A : σ.slicing.IntervalCat C a b) :=
    Slicing.IntervalCat.subobject_not_isZero_of_ne_bot C hAne
  have hAObj : ¬IsZero (A : σ.slicing.IntervalCat C a b).obj :=
    fun h => hAI (ObjectProperty.FullSubcategory.isZero_of_obj_isZero h)
  have hYObj : ¬IsZero Y.obj := by
    intro h
    have hY : IsZero Y := ObjectProperty.FullSubcategory.isZero_of_obj_isZero h
    exact hAI (IsZero.of_mono A.arrow hY)
  have hQI : ¬IsZero (cokernel A.arrow) :=
    Slicing.IntervalCat.cokernel_not_isZero_of_ne_top C hAtop hAstrict
  have hQObj : ¬IsZero (cokernel A.arrow).obj :=
    fun h => hQI (ObjectProperty.FullSubcategory.isZero_of_obj_isZero h)
  have hYwindow := hWindow Y hYObj
  have hAwindow := hWindow (A : σ.slicing.IntervalCat C a b) hAObj
  have hQwindow := hWindow (cokernel A.arrow) hQObj
  have hArange : F.phase (A : σ.slicing.IntervalCat C a b).obj ∈
      Set.Ioo (ψY - 1) (ψY + 1) := by
    constructor <;> dsimp [ψY] <;> linarith
  have hQrange : F.phase (cokernel A.arrow).obj ∈
      Set.Ioo (ψY - 1) (ψY + 1) := by
    constructor <;> dsimp [ψY] <;> linarith
  have hsum :
      F.charge (A : σ.slicing.IntervalCat C a b).obj +
          F.charge (cokernel A.arrow).obj = F.charge Y.obj := by
    have hK := Slicing.IntervalCat.K₀_of_strictShortExact C σ.slicing
      (Slicing.IntervalCat.strictShortExact_cokernel C A.arrow hAstrict)
    simpa only [charge, classOf, map_add] using
      congrArg (fun z : K₀ C => F.W (κ z)) hK.symm
  exact relativePhase_seesaw_dual hsum rfl hAphase
    (hCharge (A : σ.slicing.IntervalCat C a b).property hAObj)
    hArange hQrange

end SkewedStabilityFunction

end BridgelandStabLean.Foundation.Deformation
