/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Distance.Topology
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Mass.Subadditivity.PolygonPerimeter
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Mass.Subadditivity.CohomologyExactness
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.GLTilde.Covering.SourceTopology
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.GLTilde.Action.Stability
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Heart.Equivalence
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The Harder--Narasimhan mass-triangle chain

This file develops the stronger HN-mass subadditivity route selected for the
repository's topology comparison around Bridgeland's Proposition 8.1.

The general theorem requires the polygonal argument through the heart and
Harder--Narasimhan filtrations.  Here we establish its norm-theoretic base:

* the norm of an object's charge is bounded by its HN mass;
* charge is additive on every distinguished triangle;
* consequently the mass-triangle inequality holds when the middle object is
  semistable;
* in particular it holds when both endpoints are semistable of the same phase,
  since semistable slices are extension-closed;
* the arbitrary-left case reduces, by head--tail octahedral induction, to the
  semistable-left case.

`HNPolygon` supplies the ambient convex hull and distinguished HN path.
`ConvexPolygonPerimeter` proves the independent `t = 0` comparison of closed
vertex polygons, proves that positive-angle support maxima of the ambient HN
polygon occur on the HN path, and derives the boundary-cut mass comparison for
monomorphisms and short exact sequences. `H0ExactnessBridge` identifies the
exact heart-source obstruction as a canonical cokernel map being monic and
discharges it by proving the canonical `H⁰` and `H⁰'` functors homological.
This file proves that heart semistability agrees with the ambient slicing,
converts abelian HN filtrations into ambient HN towers with the same factor
mass, and inhabits both the phase-one boundary-heart and arbitrary-phase
semistable-left milestones.  The latter uses the six-term `H⁰` sequence and
two exact HN cutoffs to reduce to the two-cohomology window `(0, 2]`.  No open
premise is assumed as an instance or axiom.
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated Complex
open CategoryTheory.Triangulated.StabilityCondition.GroupAction Matrix
open CategoryTheory.Triangulated
open CategoryTheory.Triangulated.WeakStabilityCondition
open scoped ENNReal BigOperators ZeroObject

namespace CategoryTheory.Triangulated

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- Forget the presentation lattice while retaining the observable charge on
`K₀(C)`.  This is composition of additive homomorphisms, not an operation on
stability conditions.  It lets the ordinary heart-equivalence API be reused
for a condition defined with an arbitrary class map. -/
def StabilityCondition.WithClassMap.observable
    (σ : StabilityCondition.WithClassMap C v) : StabilityCondition C where
  slicing := σ.slicing
  Z := σ.Z.comp v
  compatible := by
    intro φ E hP hE
    simpa using σ.compat φ E hP hE
  locallyFinite := σ.locallyFinite

omit [IsTriangulated C] in
@[simp]
theorem StabilityCondition.WithClassMap.observable_slicing
    (σ : StabilityCondition.WithClassMap C v) :
    σ.observable.slicing = σ.slicing := rfl

omit [IsTriangulated C] in
@[simp]
theorem StabilityCondition.WithClassMap.observable_charge
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    σ.observable.charge E = σ.charge E := rfl

/-- The heart stability function associated to a class-map stability
condition, obtained from its observable ordinary stability condition. -/
def StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart
    (σ : StabilityCondition.WithClassMap C v) :
    @StabilityFunction (σ.slicing.toTStructure.heart.FullSubcategory) _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian) := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  refine
    { charge := fun E ↦ σ.charge E.obj
      map_zero := fun E hE ↦ σ.charge_isZero ((t.heart).ι.map_isZero hE)
      map_iso := fun {E F} e ↦ by
        exact congrArg σ.Z
          (classOf_iso C v ((t.heart).ι.mapIso e))
      additive := fun S hS ↦ by
        letI := hS.mono_f
        letI := hS.epi_g
        obtain ⟨δ, hT⟩ :=
          TStructure.heartFullSubcategory_shortExact_triangle (C := C) t
            S.f S.g S.zero (fun {W} α hα ↦ by
              have hker : IsLimit (KernelFork.ofι S.f S.zero) := hS.fIsKernel
              exact ⟨hker.lift (KernelFork.ofι α hα),
                hker.fac _ WalkingParallelPair.zero⟩)
        simpa [PreStabilityCondition.WithClassMap.charge_def] using
          congrArg σ.Z (classOf_triangle C v (Triangle.mk S.f.hom S.g.hom δ) hT)
      nonzero_mem := fun E hE ↦ by
        classical
        have hEobj : ¬IsZero E.obj := fun h ↦
          hE (ObjectProperty.FullSubcategory.isZero_of_obj_isZero h)
        have hheart := (σ.slicing.toTStructure_heart_iff C E.obj).mp E.property
        obtain ⟨F, hn, hfirst, hlast⟩ :=
          σ.slicing.exists_hn_nonzero_boundaries C hEobj
        let P := F.toPostnikovTower
        let s : Finset (Fin F.n) :=
          Finset.univ.filter (fun i ↦ ¬IsZero (P.factor i))
        have hs : s.Nonempty := by
          obtain ⟨i, hi⟩ := F.exists_nonzero_factor C hEobj
          exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
        have hminus : 0 < σ.slicing.phiMinus C E.obj hEobj :=
          σ.slicing.phiMinus_gt_of_gtProp C hEobj hheart.1
        have hplus : σ.slicing.phiPlus C E.obj hEobj ≤ 1 :=
          σ.slicing.phiPlus_le_of_leProp C hEobj hheart.2
        have hphase : ∀ i ∈ s, F.φ i ∈ Set.Ioc (0 : ℝ) 1 := by
          intro i hi
          constructor
          · calc
              0 < σ.slicing.phiMinus C E.obj hEobj := hminus
              _ = F.φ ⟨F.n - 1, by lia⟩ := by
                simpa [CategoryTheory.Triangulated.HNFiltration.phiMinus] using
                  σ.slicing.phiMinus_eq C E.obj hEobj F hn hlast
              _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
          · calc
              F.φ i ≤ F.φ ⟨0, hn⟩ :=
                F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
              _ = σ.slicing.phiPlus C E.obj hEobj := by
                simpa [CategoryTheory.Triangulated.HNFiltration.phiPlus] using
                  (σ.slicing.phiPlus_eq C E.obj hEobj F hn hfirst).symm
              _ ≤ 1 := hplus
        let f : Fin F.n → ℂ := fun i ↦ σ.charge (P.factor i)
        have hterm : ∀ i ∈ s, f i ∈ semiClosedUpperHalfPlane := by
          intro i hi
          have hne : ¬IsZero (P.factor i) := by simpa [s] using hi
          obtain ⟨m, hm, hZ⟩ := σ.compat (F.φ i) (P.factor i)
            (F.semistable i) hne
          by_cases hone : F.φ i = 1
          · right
            rw [show f i = (m : ℂ) *
                Complex.exp ((Real.pi * (1 : ℝ) : ℂ) * Complex.I) by
              simpa [f, hone] using hZ]
            constructor
            · simp [Complex.exp_mul_I]
            · simp [Complex.exp_mul_I, hm]
          · left
            have hlt : F.φ i < 1 := lt_of_le_of_ne (hphase i hi).2 hone
            rw [show f i = (m : ℂ) *
                Complex.exp ((Real.pi * F.φ i : ℝ) * Complex.I) by
              simpa [f] using hZ]
            rw [Complex.exp_ofReal_mul_I]
            change 0 < ((m : ℂ) *
              ((Real.cos (Real.pi * F.φ i) : ℂ) +
                (Real.sin (Real.pi * F.φ i) : ℂ) * Complex.I)).im
            simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re,
              Complex.ofReal_im, Complex.I_im, Complex.I_re, zero_mul, mul_zero,
              mul_one, add_zero]
            simp only [zero_add]
            exact mul_pos hm (Real.sin_pos_of_pos_of_lt_pi
              (mul_pos Real.pi_pos (hphase i hi).1)
              (by nlinarith [Real.pi_pos]))
        have hsum : σ.charge E.obj = ∑ i ∈ s, f i := by
          have hall := σ.charge_postnikovTower_eq_sum P
          rw [hall]
          let z : Finset (Fin F.n) :=
            Finset.univ.filter (fun i ↦ IsZero (P.factor i))
          have hz : ∑ i ∈ z, f i = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            simp only [z, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            exact σ.charge_isZero hi
          calc
            ∑ i, f i = (∑ i ∈ s, f i) + ∑ i ∈ z, f i := by
              simpa [s, z, f] using
                (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
                  (p := fun i : Fin F.n ↦ ¬IsZero (P.factor i)) (f := f)).symm
            _ = ∑ i ∈ s, f i := by rw [hz, add_zero]
        rw [hsum]
        exact sum_mem_semiClosedUpperHalfPlane hs hterm }

@[simp]
theorem StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_charge
    (σ : StabilityCondition.WithClassMap C v)
    (E : σ.slicing.toTStructure.heart.FullSubcategory) :
    @StabilityFunction.charge _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E = σ.charge E.obj := rfl

/-- On a nonzero heart object already lying in a slice, the phase of the
restricted owner stability function is that slice parameter. -/
theorem StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_phase_eq_of_mem_P
    (σ : StabilityCondition.WithClassMap C v) {φ : ℝ}
    (hφ : φ ∈ Set.Ioc (0 : ℝ) 1)
    (E : σ.slicing.toTStructure.heart.FullSubcategory)
    (hP : σ.slicing.P φ E.obj) (hE : ¬IsZero E) :
    @StabilityFunction.phase _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E = φ := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  have hEobj : ¬IsZero E.obj := fun hZ ↦ hE <|
    ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := E) hZ
  obtain ⟨m, hm, hZ⟩ := σ.compat φ E.obj hP hEobj
  have harg : Complex.arg
      ((m : ℂ) * Complex.exp ((Real.pi * φ : ℝ) * Complex.I)) =
      Real.pi * φ := by
    rw [Complex.arg_real_mul _ hm, Complex.arg_exp_mul_I, toIocMod_eq_self]
    constructor
    · nlinarith [Real.pi_pos, hφ.1]
    · nlinarith [Real.pi_pos, hφ.2]
  change Complex.arg (σ.charge E.obj) / Real.pi = φ
  rw [hZ, harg]
  field_simp [Real.pi_ne_zero]

/-- The heart phase is bounded by the highest ambient HN phase.  The
non-boundary case is the owner weak-charge argument bound; at phase one the
claim follows from the intrinsic range of an abelian stability phase. -/
theorem StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_phase_le_phiPlus
    (σ : StabilityCondition.WithClassMap C v)
    (E : σ.slicing.toTStructure.heart.FullSubcategory) (hE : ¬IsZero E) :
    @StabilityFunction.phase _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E ≤
      σ.slicing.phiPlus C E.obj (fun hZ ↦ hE <|
        ObjectProperty.FullSubcategory.isZero_of_obj_isZero
          (C := C) (P := σ.slicing.toTStructure.heart) (X := E) hZ) := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  have hEobj : ¬IsZero E.obj := fun hZ ↦ hE <|
    ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := E) hZ
  by_cases hplus : σ.slicing.phiPlus C E.obj hEobj < 1
  · let τ := CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.ofPre
      σ.observable.toWithClassMap
    have hbound := τ.charge_mem_upperHalfPlane_and_arg_le_phiPlus
      E.obj E.property hEobj hplus
    have harg : Complex.arg (σ.charge E.obj) ≤
        Real.pi * σ.slicing.phiPlus C E.obj hEobj := by
      simpa [τ,
        WeakPreStabilityCondition.weakStabilityFunctionOnHeart_charge,
        StabilityCondition.WithClassMap.observable,
        PreStabilityCondition.WithClassMap.charge_def] using hbound.2
    change Complex.arg (σ.charge E.obj) / Real.pi ≤ _
    exact (div_le_iff₀ Real.pi_pos).2 (by simpa [mul_comm] using harg)
  · have hheart := (σ.slicing.toTStructure_heart_iff C E.obj).mp E.property
    have hle : σ.slicing.phiPlus C E.obj hEobj ≤ 1 :=
      σ.slicing.phiPlus_le_of_leProp C hEobj hheart.2
    have heq : σ.slicing.phiPlus C E.obj hEobj = 1 :=
      le_antisymm hle (le_of_not_gt hplus)
    rw [heq]
    exact σ.observableStabilityFunctionOnHeart.phase_le_one E

/-- Ambient slice semistability implies semistability for the restricted
owner stability function on the canonical heart. -/
theorem StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_isSemistable_of_mem_P
    (σ : StabilityCondition.WithClassMap C v) {φ : ℝ}
    (hφ : φ ∈ Set.Ioc (0 : ℝ) 1)
    (E : σ.slicing.toTStructure.heart.FullSubcategory)
    (hP : σ.slicing.P φ E.obj) (hE : ¬IsZero E) :
    @StabilityFunction.IsSemistable _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  refine ⟨hE, ?_⟩
  intro B hB
  let B' : t.heart.FullSubcategory := (B : t.heart.FullSubcategory)
  have hBobj : ¬IsZero B'.obj := fun hZ ↦ hB <|
    ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := B') hZ
  have hphiPlus_le : σ.slicing.phiPlus C B'.obj hBobj ≤ φ := by
    by_contra hle
    have hgt : φ < σ.slicing.phiPlus C B'.obj hBobj := lt_of_not_ge hle
    have hBheart := (σ.slicing.toTStructure_heart_iff C B'.obj).mp B'.property
    obtain ⟨F, hn, hfirst⟩ := σ.slicing.exists_hn_nonzero_first C hBobj
    have htop : σ.slicing.phiPlus C B'.obj hBobj = F.φ ⟨0, hn⟩ := by
      simpa only [CategoryTheory.Triangulated.HNFiltration.phiPlus] using
        σ.slicing.phiPlus_eq C B'.obj hBobj F hn hfirst
    have hphase_gt : φ < F.φ ⟨0, hn⟩ := by simpa [htop] using hgt
    have hphase_mem : F.φ ⟨0, hn⟩ ∈ Set.Ioc (0 : ℝ) 1 := by
      exact ⟨hφ.1.trans hphase_gt,
        (by rw [← htop]; exact σ.slicing.phiPlus_le_of_leProp C hBobj hBheart.2)⟩
    have hAheart : t.heart (F.factor ⟨0, hn⟩) := by
      rw [σ.slicing.toTStructure_heart_iff C]
      exact ⟨σ.slicing.gtProp_of_semistable C (F.semistable ⟨0, hn⟩)
          hphase_mem.1,
        σ.slicing.leProp_of_semistable C (F.semistable ⟨0, hn⟩)
          hphase_mem.2⟩
    obtain ⟨α, hα⟩ : ∃ α : F.factor ⟨0, hn⟩ ⟶ B'.obj, α ≠ 0 := by
      by_contra hzero
      push Not at hzero
      exact hfirst (F.firstFactor_isZero_of_hom_eq_zero C σ.slicing hn hzero)
    let A : t.heart.FullSubcategory := ⟨F.factor ⟨0, hn⟩, hAheart⟩
    let αH : A ⟶ B' := ObjectProperty.homMk α
    have hcomp : α ≫ B.arrow.hom ≠ 0 := by
      intro hzero
      have hz : αH ≫ B.arrow = 0 := by ext; exact hzero
      have : αH = 0 := (cancel_mono B.arrow).mp (by simpa using hz)
      exact hα (by simpa [αH] using congrArg (fun f ↦ f.hom) this)
    exact hcomp <| σ.slicing.hom_vanishing _ _ _ _ hphase_gt
      (F.semistable ⟨0, hn⟩) hP (α ≫ B.arrow.hom)
  calc
    σ.observableStabilityFunctionOnHeart.phase B' ≤
        σ.slicing.phiPlus C B'.obj hBobj :=
      σ.observableStabilityFunctionOnHeart_phase_le_phiPlus B' hB
    _ ≤ φ := hphiPlus_le
    _ = σ.observableStabilityFunctionOnHeart.phase E :=
      (σ.observableStabilityFunctionOnHeart_phase_eq_of_mem_P hφ E hP hE).symm

/-- The observable heart stability function has Harder--Narasimhan
filtrations. -/
theorem StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_hasHN
    (σ : StabilityCondition.WithClassMap C v) :
    @StabilityFunction.HasHNProperty
      (σ.slicing.toTStructure.heart.FullSubcategory) _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let Z := σ.observableStabilityFunctionOnHeart
  intro E hE
  have hEobj : ¬IsZero E.obj := fun hZ ↦ hE <|
    ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := E) hZ
  suffices hmain :
      ∀ (m : ℕ) {X : t.heart.FullSubcategory} (hXobj : ¬IsZero X.obj)
        (F : HNFiltration C σ.slicing.P X.obj) (hnF : 0 < F.n)
        (hFm : F.n ≤ m) (hfirst : ¬IsZero (F.factor ⟨0, hnF⟩)),
        ∃ G : AbelianHNFiltration Z X,
          G.phase ⟨G.n - 1, by have := G.nonempty; omega⟩ =
            σ.slicing.phiMinus C X.obj hXobj by
    obtain ⟨F, hnF, hfirst, -⟩ :=
      σ.slicing.exists_hn_nonzero_boundaries C hEobj
    exact ⟨(hmain F.n hEobj F hnF le_rfl hfirst).choose⟩
  intro m
  induction m with
  | zero =>
      intro X hXobj F hnF hFm
      omega
  | succ m ih =>
      intro X hXobj F hnF hFm hfirst
      have hX : ¬IsZero X := fun hZ ↦ hXobj ((t.heart).ι.map_isZero hZ)
      have hXheart := (σ.slicing.toTStructure_heart_iff C X.obj).mp X.property
      by_cases h1 : F.n = 1
      · let φ := F.φ ⟨0, hnF⟩
        have hlast : ¬IsZero (F.factor ⟨F.n - 1, by omega⟩) := by
          have hidx : (⟨F.n - 1, by omega⟩ : Fin F.n) = ⟨0, hnF⟩ :=
            Fin.ext (by omega)
          simpa [hidx] using hfirst
        have hall : ∀ i : Fin F.n, F.φ i = φ := by
          intro i
          have hi : i = ⟨0, hnF⟩ := Fin.ext (by omega)
          subst i
          rfl
        have hP : σ.slicing.P φ X.obj :=
          σ.slicing.semistable_of_HN_all_eq C F hall
        have hφm : σ.slicing.phiMinus C X.obj hXobj = φ := by
          rw [σ.slicing.phiMinus_eq C X.obj hXobj F hnF hlast]
          simp only [CategoryTheory.Triangulated.HNFiltration.phiMinus]
          congr 1
          exact Fin.ext (by omega)
        have hφp : σ.slicing.phiPlus C X.obj hXobj = φ := by
          simpa only [CategoryTheory.Triangulated.HNFiltration.phiPlus] using
            σ.slicing.phiPlus_eq C X.obj hXobj F hnF hfirst
        have hφ : φ ∈ Set.Ioc (0 : ℝ) 1 := by
          constructor
          · exact (by
              have := σ.slicing.phiMinus_gt_of_gtProp C hXobj hXheart.1
              linarith)
          · exact (by
              have := σ.slicing.phiPlus_le_of_leProp C hXobj hXheart.2
              linarith)
        have hss : @StabilityFunction.IsSemistable _ _
            t.heartFullSubcategoryAbelian Z X :=
          σ.observableStabilityFunctionOnHeart_isSemistable_of_mem_P
            hφ X hP hX
        obtain ⟨G, hG⟩ :=
          CategoryTheory.Triangulated.StabilityFunction.exists_hn_with_last_phase_of_semistable
            Z hss
        refine ⟨G, ?_⟩
        calc
          G.phase ⟨G.n - 1, by have := G.nonempty; omega⟩ = Z.phase X := hG
          _ = φ :=
            σ.observableStabilityFunctionOnHeart_phase_eq_of_mem_P hφ X hP hX
          _ = σ.slicing.phiMinus C X.obj hXobj := hφm.symm
      · have htwo : 2 ≤ F.n := by omega
        by_cases hlast : IsZero (F.factor ⟨F.n - 1, by omega⟩)
        · let F' := F.dropLast C (by omega) hlast
          have hnF' : 0 < F'.n := F'.n_pos C hXobj
          have hF'm : F'.n ≤ m := by
            change F.n - 1 ≤ m
            omega
          have hfirst' : ¬IsZero (F'.factor ⟨0, hnF'⟩) := by
            change ¬IsZero (F.factor ⟨0, by omega⟩)
            simpa using hfirst
          exact ih hXobj F' hnF' hF'm hfirst'
        · have hall_mem : ∀ i : Fin F.n, F.φ i ∈ Set.Ioc (0 : ℝ) 1 := by
            intro i
            constructor
            · calc
                0 < σ.slicing.phiMinus C X.obj hXobj :=
                  σ.slicing.phiMinus_gt_of_gtProp C hXobj hXheart.1
                _ = F.φ ⟨F.n - 1, by omega⟩ := by
                  simpa only [CategoryTheory.Triangulated.HNFiltration.phiMinus]
                    using σ.slicing.phiMinus_eq C X.obj hXobj F hnF hlast
                _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
            · calc
                F.φ i ≤ F.φ ⟨0, hnF⟩ :=
                  F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
                _ = σ.slicing.phiPlus C X.obj hXobj := by
                  simpa only [CategoryTheory.Triangulated.HNFiltration.phiPlus]
                    using (σ.slicing.phiPlus_eq C X.obj hXobj F hnF hfirst).symm
                _ ≤ 1 := σ.slicing.phiPlus_le_of_leProp C hXobj hXheart.2
          let FX : HNFiltration C σ.slicing.P
              (F.chain.obj ⟨F.n - 1, by omega⟩) :=
            F.prefix C (F.n - 1) (by omega)
          have hFXn : 0 < FX.n := by change 0 < F.n - 1; omega
          have hFXheart : t.heart (F.chain.obj ⟨F.n - 1, by omega⟩) := by
            rw [σ.slicing.toTStructure_heart_iff C]
            exact ⟨
              CategoryTheory.Triangulated.HNFiltration.chain_obj_gtProp
                C σ.slicing F (F.n - 1) (by omega) (by omega) 0
                (fun j ↦ (hall_mem ⟨j, by omega⟩).1),
              CategoryTheory.Triangulated.HNFiltration.chain_obj_leProp
                C σ.slicing F (F.n - 1) (by omega) (by omega) 1
                (fun j ↦ (hall_mem ⟨j, by omega⟩).2)⟩
          let X' : t.heart.FullSubcategory :=
            ⟨F.chain.obj ⟨F.n - 1, by omega⟩, hFXheart⟩
          have hfirstFX : ¬IsZero (FX.factor ⟨0, hFXn⟩) := by
            change ¬IsZero (F.factor ⟨0, by omega⟩)
            simpa using hfirst
          have hX'obj : ¬IsZero X'.obj := by
            intro hZ
            have hz : ∀ f : FX.factor ⟨0, hFXn⟩ ⟶ X'.obj, f = 0 :=
              fun f ↦ hZ.eq_of_tgt _ _
            exact hfirstFX <| FX.firstFactor_isZero_of_hom_eq_zero
              C σ.slicing hFXn hz
          obtain ⟨GX, hGX⟩ := ih hX'obj FX hFXn (by
            change F.n - 1 ≤ m
            omega) hfirstFX
          let jLast : Fin F.n := ⟨F.n - 1, by omega⟩
          have hBheart : t.heart (F.factor jLast) := by
            rw [σ.slicing.toTStructure_heart_iff C]
            exact ⟨σ.slicing.gtProp_of_semistable C (F.semistable jLast)
                (hall_mem jLast).1,
              σ.slicing.leProp_of_semistable C (F.semistable jLast)
                (hall_mem jLast).2⟩
          let B : t.heart.FullSubcategory := ⟨F.factor jLast, hBheart⟩
          have hB : ¬IsZero B := fun hZ ↦ hlast ((t.heart).ι.map_isZero hZ)
          have hBss : @StabilityFunction.IsSemistable _ _
              t.heartFullSubcategoryAbelian Z B :=
            σ.observableStabilityFunctionOnHeart_isSemistable_of_mem_P
              (hall_mem jLast) B (F.semistable jLast) hB
          have hBphase : Z.phase B = F.φ jLast :=
            σ.observableStabilityFunctionOnHeart_phase_eq_of_mem_P
              (hall_mem jLast) B (F.semistable jLast) hB
          have hX'gt : σ.slicing.gtProp C (F.φ jLast) X'.obj :=
            CategoryTheory.Triangulated.HNFiltration.chain_obj_gtProp
              C σ.slicing F (F.n - 1) (by omega) (by omega) (F.φ jLast) <|
                fun j ↦ F.hφ (Fin.mk_lt_mk.mpr (by omega))
          have hphase_lt : Z.phase B < GX.phase ⟨GX.n - 1, by
              have := GX.nonempty; omega⟩ := by
            calc
              Z.phase B = F.φ jLast := hBphase
              _ < σ.slicing.phiMinus C X'.obj hX'obj :=
                σ.slicing.phiMinus_gt_of_gtProp C hX'obj hX'gt
              _ = GX.phase ⟨GX.n - 1, by have := GX.nonempty; omega⟩ := hGX.symm
          let Tlast := F.triangle jLast
          let e₁ := Classical.choice (F.triangle_obj₁ jLast)
          let e₂ := Classical.choice (F.triangle_obj₂ jLast)
          have hobj₂_eq : F.chain.obj' (F.n - 1 + 1) (by omega) =
              F.chain.right := by
            simp only [ComposableArrows.obj']
            congr 1
            ext
            simp
            omega
          let e₂X : Tlast.obj₂ ≅ X.obj :=
            e₂.trans ((eqToIso hobj₂_eq).trans (Classical.choice F.top_iso))
          let i : X' ⟶ X :=
            ObjectProperty.homMk (e₁.inv ≫ Tlast.mor₁ ≫ e₂X.hom)
          let q : X ⟶ B := ObjectProperty.homMk (e₂X.inv ≫ Tlast.mor₂)
          let δ : B.obj ⟶ X'.obj⟦(1 : ℤ)⟧ := Tlast.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
          have hTlast : Triangle.mk i.hom q.hom δ ∈ distTriang C := by
            refine isomorphic_distinguished _ (F.triangle_dist jLast) _ ?_
            exact Triangle.isoMk _ _ e₁.symm e₂X.symm (Iso.refl _)
              (by simp [Tlast, i, e₂X]) (by simp [Tlast, q, e₂X])
              (by simp [Tlast, δ])
          have hiq : i ≫ q = 0 := by
            ext
            simpa using comp_distTriang_mor_zero₁₂ _ hTlast
          have hKer : IsLimit (KernelFork.ofι i hiq) := by
            simpa [hiq] using
              Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
                (CategoryTheory.Triangulated.TStructure.heart_hι t)
                i q δ hTlast
          have hCok : IsColimit (CokernelCofork.ofπ q hiq) := by
            simpa [hiq] using
              Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
                (CategoryTheory.Triangulated.TStructure.heart_hι t)
                i q δ hTlast
          let eB : cokernel i ≅ B :=
            IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel i) hCok
          haveI : Mono i := Fork.IsLimit.mono hKer
          obtain ⟨G, hG⟩ :=
            CategoryTheory.Triangulated.StabilityFunction.append_hn_filtration_of_mono
              Z i GX eB hBss hphase_lt
          refine ⟨G, ?_⟩
          calc
            G.phase ⟨G.n - 1, by have := G.nonempty; omega⟩ = Z.phase B := hG
            _ = F.φ jLast := hBphase
            _ = σ.slicing.phiMinus C X.obj hXobj := by
              symm
              simpa only [CategoryTheory.Triangulated.HNFiltration.phiMinus]
                using σ.slicing.phiMinus_eq C X.obj hXobj F hnF hlast

/-- The converse half of the heart/slicing semistability comparison.  A
nonzero object that is semistable for the stability function on the canonical
heart is semistable in the ambient slicing, at the same phase. -/
theorem StabilityCondition.WithClassMap.mem_slicing_of_heart_isSemistable
    (σ : StabilityCondition.WithClassMap C v)
    (E : σ.slicing.toTStructure.heart.FullSubcategory)
    (hE : @StabilityFunction.IsSemistable _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E) :
    σ.slicing.P (@StabilityFunction.phase _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E) E.obj := by
  let t := σ.slicing.toTStructure
  let Z := σ.observableStabilityFunctionOnHeart
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  have hEnz : ¬IsZero E := hE.1
  have hEobj : ¬IsZero E.obj := fun hZ ↦ hEnz <|
    ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := E) hZ
  have hEheart := (σ.slicing.toTStructure_heart_iff C E.obj).mp E.property
  obtain ⟨F, hn, hfirst, hlast⟩ :=
    σ.slicing.exists_hn_nonzero_boundaries C hEobj
  have hall_mem : ∀ i : Fin F.n, F.φ i ∈ Set.Ioc (0 : ℝ) 1 := by
    intro i
    constructor
    · calc
        0 < σ.slicing.phiMinus C E.obj hEobj :=
          σ.slicing.phiMinus_gt_of_gtProp C hEobj hEheart.1
        _ = F.φ ⟨F.n - 1, by lia⟩ :=
          σ.slicing.phiMinus_eq C E.obj hEobj F hn hlast
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
    · calc
        F.φ i ≤ F.φ ⟨0, hn⟩ :=
          F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        _ = σ.slicing.phiPlus C E.obj hEobj := by
          symm
          exact σ.slicing.phiPlus_eq C E.obj hEobj F hn hfirst
        _ ≤ 1 := σ.slicing.phiPlus_le_of_leProp C hEobj hEheart.2
  let iFirst : Fin F.n := ⟨0, hn⟩
  have hAheart : t.heart (F.triangle iFirst).obj₃ := by
    rw [σ.slicing.toTStructure_heart_iff C]
    exact ⟨σ.slicing.gtProp_of_semistable C
        (F.semistable iFirst) (hall_mem iFirst).1,
      σ.slicing.leProp_of_semistable C
        (F.semistable iFirst) (hall_mem iFirst).2⟩
  let A : t.heart.FullSubcategory := ⟨(F.triangle iFirst).obj₃, hAheart⟩
  have hAnz : ¬IsZero A := fun hZ ↦ hfirst ((t.heart).ι.map_isZero hZ)
  have hAss : @StabilityFunction.IsSemistable _ _
      t.heartFullSubcategoryAbelian Z A :=
    σ.observableStabilityFunctionOnHeart_isSemistable_of_mem_P
      (hall_mem iFirst) A (F.semistable iFirst) hAnz
  have hAphase : Z.phase A = F.φ iFirst :=
    σ.observableStabilityFunctionOnHeart_phase_eq_of_mem_P
      (hall_mem iFirst) A (F.semistable iFirst) hAnz
  have hα : ∃ α : A.obj ⟶ E.obj, α ≠ 0 := by
    by_contra hzero
    push Not at hzero
    exact hfirst <|
      F.isZero_factor_zero_of_hom_eq_zero C σ.slicing hn hzero
  obtain ⟨α, hα⟩ := hα
  let αH : A ⟶ E := ObjectProperty.homMk α
  have hIm : ¬IsZero (Limits.image αH) := by
    intro hZ
    apply hα
    have hι : Limits.image.ι αH = 0 := zero_of_source_iso_zero _ hZ.isoZero
    have hαH : αH = 0 := by rw [← Limits.image.fac αH, hι, comp_zero]
    exact congr_arg (·.hom) hαH
  have hImSub : ¬IsZero (imageSubobject αH : t.heart.FullSubcategory) := by
    intro hZ
    exact hIm (hZ.of_iso (imageSubobjectIso αH).symm)
  have hfirst_le : F.φ iFirst ≤ Z.phase E := by
    rw [← hAphase]
    calc
      Z.phase A ≤ Z.phase (Limits.image αH) :=
        Z.phase_le_of_epi (factorThruImage αH) hAss hIm
      _ = Z.phase (imageSubobject αH : t.heart.FullSubcategory) :=
        Z.phase_eq_of_iso (imageSubobjectIso αH).symm
      _ ≤ Z.phase E := hE.2 (imageSubobject αH) hImSub
  have hplus_le : σ.slicing.phiPlus C E.obj hEobj ≤ Z.phase E := by
    rw [σ.slicing.phiPlus_eq C E.obj hEobj F hn hfirst]
    exact hfirst_le

  let jLast : Fin F.n := ⟨F.n - 1, by lia⟩
  have hXheart : t.heart (F.chain.obj ⟨F.n - 1, by lia⟩) := by
    by_cases hk : F.n - 1 = 0
    · rw [σ.slicing.toTStructure_heart_iff C]
      have hidx : (⟨F.n - 1, by lia⟩ : Fin (F.n + 1)) = 0 :=
        Fin.ext (by simpa using hk)
      have hzero : IsZero (F.chain.obj ⟨F.n - 1, by lia⟩) := by
        rw [hidx]
        simpa [ComposableArrows.left] using F.base_isZero
      exact ⟨Or.inl hzero, Or.inl hzero⟩
    · rw [σ.slicing.toTStructure_heart_iff C]
      constructor
      · exact CategoryTheory.Triangulated.HNFiltration.chain_obj_gtProp
          C σ.slicing F (F.n - 1)
          (by lia) (Nat.pos_of_ne_zero hk) 0
          (fun j ↦ (hall_mem ⟨j, by lia⟩).1)
      · exact CategoryTheory.Triangulated.HNFiltration.chain_obj_leProp
          C σ.slicing F (F.n - 1)
          (by lia) (Nat.pos_of_ne_zero hk) 1
          (fun j ↦ (hall_mem ⟨j, by lia⟩).2)
  let X : t.heart.FullSubcategory :=
    ⟨F.chain.obj ⟨F.n - 1, by lia⟩, hXheart⟩
  have hBheart : t.heart (F.triangle jLast).obj₃ := by
    rw [σ.slicing.toTStructure_heart_iff C]
    exact ⟨σ.slicing.gtProp_of_semistable C
        (F.semistable jLast) (hall_mem jLast).1,
      σ.slicing.leProp_of_semistable C
        (F.semistable jLast) (hall_mem jLast).2⟩
  let B : t.heart.FullSubcategory := ⟨(F.triangle jLast).obj₃, hBheart⟩
  have hBnz : ¬IsZero B := fun hZ ↦ hlast ((t.heart).ι.map_isZero hZ)
  have hBphase : Z.phase B = F.φ jLast :=
    σ.observableStabilityFunctionOnHeart_phase_eq_of_mem_P
      (hall_mem jLast) B (F.semistable jLast) hBnz
  let Tlast := F.triangle jLast
  let e₁ := Classical.choice (F.triangle_obj₁ jLast)
  let e₂ := Classical.choice (F.triangle_obj₂ jLast)
  have hobj₂_eq : F.chain.obj' (F.n - 1 + 1) (by lia) = F.chain.right := by
    simp only [ComposableArrows.obj']
    congr 1
    ext
    simp
    lia
  let e₂E : Tlast.obj₂ ≅ E.obj :=
    e₂.trans ((eqToIso hobj₂_eq).trans (Classical.choice F.top_iso))
  let i : X ⟶ E := ObjectProperty.homMk
    (e₁.inv ≫ Tlast.mor₁ ≫ e₂E.hom)
  let q : E ⟶ B := ObjectProperty.homMk (e₂E.inv ≫ Tlast.mor₂)
  let δ : B.obj ⟶ X.obj⟦(1 : ℤ)⟧ := Tlast.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
  have hTlast : Triangle.mk i.hom q.hom δ ∈ distTriang C := by
    refine isomorphic_distinguished _ (F.triangle_dist jLast) _ ?_
    exact Triangle.isoMk _ _ e₁.symm e₂E.symm (Iso.refl _)
      (by simp [Tlast, i, e₂E]) (by simp [Tlast, q, e₂E])
      (by simp [Tlast, δ])
  have hiq_hom : i.hom ≫ q.hom = 0 := by
    simpa using comp_distTriang_mor_zero₁₂ _ hTlast
  have hiq : i ≫ q = 0 := by
    ext
    exact hiq_hom
  have hCok : IsColimit (CokernelCofork.ofπ q hiq) := by
    simpa [hiq] using
      Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
        (CategoryTheory.Triangulated.TStructure.heart_hι t)
        i q δ hTlast
  letI : Epi q := Cofork.IsColimit.epi hCok
  have hlast_ge : Z.phase E ≤ F.φ jLast := by
    rw [← hBphase]
    exact Z.phase_le_of_epi q hE hBnz
  have hminus_ge : Z.phase E ≤ σ.slicing.phiMinus C E.obj hEobj := by
    rw [σ.slicing.phiMinus_eq C E.obj hEobj F hn hlast]
    exact hlast_ge
  have hextreme : σ.slicing.phiPlus C E.obj hEobj =
      σ.slicing.phiMinus C E.obj hEobj := by
    apply le_antisymm
    · exact hplus_le.trans hminus_ge
    · exact σ.slicing.phiMinus_le_phiPlus C E.obj hEobj
  have hP := σ.slicing.semistable_of_phiPlus_eq_phiMinus (C := C) hEobj hextreme
  rwa [show σ.slicing.phiPlus C E.obj hEobj = Z.phase E from
    le_antisymm hplus_le
      (σ.observableStabilityFunctionOnHeart_phase_le_phiPlus E hEnz)] at hP

/-- The norm of the total charge is at most the sum of the norms of the
Harder--Narasimhan factor charges. -/
theorem norm_charge_le_stabilityMass_toReal
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    ‖σ.charge E‖ ≤ (stabilityMass σ E).toReal := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [σ.charge_postnikovTower_eq_sum F.toPostnikovTower,
    stabilityMass_toReal_eq_sum σ F]
  exact norm_sum_le _ _

omit [IsTriangulated C] in
/-- Shifting an HN filtration by one does not change its mass. -/
theorem HNFiltration.mass_shift_one
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) :
    (F.shift C σ.slicing 1).mass σ = F.mass σ := by
  unfold HNFiltration.mass
  apply Finset.sum_congr rfl
  intro i _
  simp only [CategoryTheory.Triangulated.HNFiltration.shift]
  change ENNReal.ofReal ‖σ.charge ((F.triangle i).obj₃⟦(1 : ℤ)⟧)‖ =
    ENNReal.ofReal ‖σ.charge (F.triangle i).obj₃‖
  simp only [PreStabilityCondition.WithClassMap.charge_def,
    classOf_shift_one, map_neg, norm_neg]

/-- Shifting an object by one does not change its HN mass. -/
@[simp]
theorem stabilityMass_shift_one
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    stabilityMass σ (E⟦(1 : ℤ)⟧) = stabilityMass σ E := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [stabilityMass_eq_mass σ (F.shift C σ.slicing 1),
    stabilityMass_eq_mass σ F]
  exact CategoryTheory.Triangulated.HNFiltration.mass_shift_one σ F

omit [IsTriangulated C] in
/-- Shifting an HN filtration by minus one does not change its mass. -/
theorem HNFiltration.mass_shift_neg_one
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) :
    (F.shift C σ.slicing (-1)).mass σ = F.mass σ := by
  unfold HNFiltration.mass
  apply Finset.sum_congr rfl
  intro i _
  simp only [CategoryTheory.Triangulated.HNFiltration.shift]
  change ENNReal.ofReal ‖σ.charge ((F.triangle i).obj₃⟦(-1 : ℤ)⟧)‖ =
    ENNReal.ofReal ‖σ.charge (F.triangle i).obj₃‖
  simp only [PreStabilityCondition.WithClassMap.charge_def,
    classOf_shift_neg_one, map_neg, norm_neg]

/-- Shifting an object by minus one does not change its HN mass. -/
@[simp]
theorem stabilityMass_shift_neg_one
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    stabilityMass σ (E⟦(-1 : ℤ)⟧) = stabilityMass σ E := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [stabilityMass_eq_mass σ (F.shift C σ.slicing (-1)),
    stabilityMass_eq_mass σ F]
  exact CategoryTheory.Triangulated.HNFiltration.mass_shift_neg_one σ F

/-! ### Invariance under lifted rotations -/

/-- A rotation matrix acts on the complex plane by multiplication by the
unit complex number with the corresponding angle. -/
theorem actC_rotationGLPos (θ : ℝ) (z : ℂ) :
    actC (rotationGLPos θ) z = cexpI (Real.pi * θ) * z := by
  apply cplxCoord.injective
  rw [actC_apply, LinearEquiv.apply_symm_apply, rotationGLPos_mat]
  simp only [cplxCoord_apply]
  ext i
  fin_cases i <;>
    simp [rotationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      cexpI_re, cexpI_im, Complex.mul_re, Complex.mul_im] <;> ring

/-- Rotations preserve the complex norm used in each HN mass summand. -/
theorem norm_actC_rotationGLPos (θ : ℝ) (z : ℂ) :
    ‖actC (rotationGLPos θ) z‖ = ‖z‖ := by
  rw [actC_rotationGLPos, norm_mul, norm_cexpI, one_mul]

/-- Relabel an HN filtration after acting on its stability condition by a
lifted rotation.  The tower is unchanged and every phase is translated by
`θ`. -/
def HNFiltration.rotateStability
    (σ : StabilityCondition.WithClassMap C v) {θ : ℝ} {E : C}
    (F : HNFiltration C σ.slicing.P E) :
    HNFiltration C (liftedRotation θ • σ).slicing.P E where
  n := F.n
  chain := F.chain
  triangle := F.triangle
  triangle_dist := F.triangle_dist
  triangle_obj₁ := F.triangle_obj₁
  triangle_obj₂ := F.triangle_obj₂
  base_isZero := F.base_isZero
  top_iso := F.top_iso
  φ := fun i ↦ F.φ i + θ
  hφ := by intro i j hij; linarith [F.hφ hij]
  semistable := by
    intro i
    change σ.slicing.P ((phaseTranslation θ)⁻¹.toOrderIso (F.φ i + θ)) _
    change σ.slicing.P (F.φ i + θ - θ) _
    simpa using F.semistable i

/-- Undo the phase relabelling of an HN filtration for a rotated stability
condition. -/
def HNFiltration.unrotateStability
    (σ : StabilityCondition.WithClassMap C v) {θ : ℝ} {E : C}
    (F : HNFiltration C (liftedRotation θ • σ).slicing.P E) :
    HNFiltration C σ.slicing.P E where
  n := F.n
  chain := F.chain
  triangle := F.triangle
  triangle_dist := F.triangle_dist
  triangle_obj₁ := F.triangle_obj₁
  triangle_obj₂ := F.triangle_obj₂
  base_isZero := F.base_isZero
  top_iso := F.top_iso
  φ := fun i ↦ F.φ i - θ
  hφ := by intro i j hij; linarith [F.hφ hij]
  semistable := by
    intro i
    have hi := F.semistable i
    change σ.slicing.P ((phaseTranslation θ)⁻¹.toOrderIso (F.φ i)) _ at hi
    change σ.slicing.P (F.φ i - θ) _ at hi
    exact hi

/-- Relabelling an HN filtration by a lifted rotation preserves its finite
mass sum. -/
theorem HNFiltration.mass_rotateStability
    (σ : StabilityCondition.WithClassMap C v) {θ : ℝ} {E : C}
    (F : HNFiltration C σ.slicing.P E) :
    (F.rotateStability σ (θ := θ)).mass (liftedRotation θ • σ) = F.mass σ := by
  unfold HNFiltration.mass
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change ‖actC (rotationGLPos θ) (σ.charge (F.factor i))‖ = _
  exact norm_actC_rotationGLPos θ _

/-- Undoing a lifted rotation also preserves the finite HN mass sum. -/
theorem HNFiltration.mass_unrotateStability
    (σ : StabilityCondition.WithClassMap C v) {θ : ℝ} {E : C}
    (F : HNFiltration C (liftedRotation θ • σ).slicing.P E) :
    (F.unrotateStability σ).mass σ = F.mass (liftedRotation θ • σ) := by
  unfold HNFiltration.mass
  apply Finset.sum_congr rfl
  intro i _
  dsimp [HNFiltration.unrotateStability, PostnikovTower.factor]
  change ENNReal.ofReal ‖σ.charge (F.factor i)‖ =
    ENNReal.ofReal ‖actC (rotationGLPos θ) (σ.charge (F.factor i))‖
  rw [norm_actC_rotationGLPos]

/-- Acting on a stability condition by a pure lifted rotation leaves the HN
mass of every object unchanged. -/
@[simp]
theorem stabilityMass_liftedRotation
    (σ : StabilityCondition.WithClassMap C v) (θ : ℝ) (E : C) :
    stabilityMass (liftedRotation θ • σ) E = stabilityMass σ E := by
  apply le_antisymm
  · refine iSup_le fun F ↦ ?_
    rw [← F.mass_unrotateStability σ]
    exact le_iSup (fun G : HNFiltration C σ.slicing.P E ↦ G.mass σ)
      (F.unrotateStability σ)
  · refine iSup_le fun F ↦ ?_
    rw [← F.mass_rotateStability σ (θ := θ)]
    exact le_iSup
      (fun G : HNFiltration C (liftedRotation θ • σ).slicing.P E ↦
        G.mass (liftedRotation θ • σ))
      (F.rotateStability σ)

/-! ### Exact mass splitting across a phase cutoff -/

omit [IsTriangulated C] in
/-- Appending one strictly lower semistable factor to an HN filtration adds
exactly the norm of that factor's charge to the finite mass. -/
theorem HNFiltration.mass_appendFactor
    (σ : StabilityCondition.WithClassMap C v)
    {X E : C} (GX : HNFiltration C σ.slicing.P X)
    (T : Triangle C) (hT : T ∈ distTriang C)
    (eT₁ : T.obj₁ ≅ X) (eT₂ : T.obj₂ ≅ E)
    (ψ : ℝ) (hψ : σ.slicing.P ψ T.obj₃)
    (hψ_lt : ∀ j : Fin GX.n, ψ < GX.φ j) :
    (GX.appendFactor C T hT eT₁ eT₂ ψ hψ hψ_lt).mass σ =
      GX.mass σ + ENNReal.ofReal ‖σ.charge T.obj₃‖ := by
  unfold HNFiltration.mass
  change (∑ i : Fin (GX.n + 1),
      ENNReal.ofReal ‖σ.charge
        ((GX.appendFactor C T hT eT₁ eT₂ ψ hψ hψ_lt).factor i)‖) = _
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp [HNFiltration.appendFactor, PostnikovTower.factor, i.isLt]
  · simp [HNFiltration.appendFactor, PostnikovTower.factor]

/-- Real-valued ambient form of `HNFiltration.mass_appendFactor`. -/
theorem stabilityMass_toReal_appendFactor
    (σ : StabilityCondition.WithClassMap C v)
    {X E : C} (GX : HNFiltration C σ.slicing.P X)
    (T : Triangle C) (hT : T ∈ distTriang C)
    (eT₁ : T.obj₁ ≅ X) (eT₂ : T.obj₂ ≅ E)
    (ψ : ℝ) (hψ : σ.slicing.P ψ T.obj₃)
    (hψ_lt : ∀ j : Fin GX.n, ψ < GX.φ j) :
    (stabilityMass σ E).toReal =
      (stabilityMass σ X).toReal + ‖σ.charge T.obj₃‖ := by
  let G := GX.appendFactor C T hT eT₁ eT₂ ψ hψ hψ_lt
  rw [stabilityMass_eq_mass σ G, stabilityMass_eq_mass σ GX]
  dsimp [G]
  change (CategoryTheory.Triangulated.HNFiltration.mass σ
      (CategoryTheory.Triangulated.HNFiltration.appendFactor
        C GX T hT eT₁ eT₂ ψ hψ hψ_lt)).toReal =
    (CategoryTheory.Triangulated.HNFiltration.mass σ GX).toReal +
      ‖σ.charge T.obj₃‖
  have hm := CategoryTheory.Triangulated.HNFiltration.mass_appendFactor
    σ GX T hT eT₁ eT₂ ψ hψ hψ_lt
  calc
    (CategoryTheory.Triangulated.HNFiltration.mass σ
        (CategoryTheory.Triangulated.HNFiltration.appendFactor
          C GX T hT eT₁ eT₂ ψ hψ hψ_lt)).toReal =
        (CategoryTheory.Triangulated.HNFiltration.mass σ GX +
          ENNReal.ofReal ‖σ.charge T.obj₃‖).toReal :=
      congrArg ENNReal.toReal hm
    _ = (CategoryTheory.Triangulated.HNFiltration.mass σ GX).toReal +
        ‖σ.charge T.obj₃‖ := by
      rw [ENNReal.toReal_add]
      · simp
      · simp [CategoryTheory.Triangulated.HNFiltration.mass,
          CategoryTheory.Triangulated.HNFiltration.mass]
      · exact ENNReal.ofReal_ne_top

/-- HN mass is exactly additive across a distinguished triangle when every
phase of the right-hand HN filtration is strictly below every phase of the
left-hand filtration.  The proof peels the right filtration from its head
and uses the octahedral axiom to append that factor to the left filtration. -/
theorem stabilityMass_toReal_triangle_eq_add_of_hn_separated
    (σ : StabilityCondition.WithClassMap C v)
    {X E Y : C}
    (GX : HNFiltration C σ.slicing.P X)
    (GY : HNFiltration C σ.slicing.P Y)
    (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang C)
    (hsep : ∀ i : Fin GY.n, ∀ j : Fin GX.n, GY.φ i < GX.φ j) :
    (stabilityMass σ E).toReal =
      (stabilityMass σ X).toReal + (stabilityMass σ Y).toReal := by
  suffices hmain :
      ∀ (m : ℕ) {X Y : C}
        (GX : HNFiltration C σ.slicing.P X)
        (GY : HNFiltration C σ.slicing.P Y), GY.n ≤ m →
        ∀ {E : C} (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang C →
          (∀ i : Fin GY.n, ∀ j : Fin GX.n, GY.φ i < GX.φ j) →
          (stabilityMass σ E).toReal =
            (stabilityMass σ X).toReal + (stabilityMass σ Y).toReal by
    exact hmain GY.n GX GY le_rfl f g h hT hsep
  intro m
  induction m with
  | zero =>
      intro X Y GX GY hn E f g h hT _hsep
      have hYn : GY.n = 0 := by omega
      have hYz : IsZero Y := GY.isZero_of_length_zero hYn
      haveI : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hYz
      rw [stabilityMass_congr σ (asIso f)]
      rw [show stabilityMass σ Y = 0 from
        (stabilityMass_eq_zero_iff σ Y).2 hYz]
      simp
  | succ m ih =>
      intro X Y GX GY hn E f g h hT hsep
      by_cases hYn : GY.n = 0
      · have hYz : IsZero Y := GY.isZero_of_length_zero hYn
        haveI : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hYz
        rw [stabilityMass_congr σ (asIso f)]
        rw [show stabilityMass σ Y = 0 from
          (stabilityMass_eq_zero_iff σ Y).2 hYz]
        simp
      · have hYpos : 0 < GY.n := Nat.pos_of_ne_zero hYn
        obtain ⟨Ytail, Gtail, a, b, c, hHead, hmassY, hnTail, hφTail⟩ :=
          GY.exists_headTail_mass σ hYpos
        obtain ⟨Z, fZE, hYZ, hZE⟩ := distinguished_cocone_triangle₁ (g ≫ b)
        let oct := Triangulated.someOctahedron'
          (show g ≫ b = g ≫ b by rfl) hT hHead hZE
        let iHead : Fin GY.n := ⟨0, hYpos⟩
        have hsepHead : ∀ j : Fin GX.n, GY.φ iHead < GX.φ j :=
          fun j ↦ hsep iHead j
        let GZ := GX.appendFactor C oct.triangle oct.mem
          (Iso.refl _) (Iso.refl _) (GY.φ iHead) (GY.semistable iHead) hsepHead
        have hmassZ :
            (stabilityMass σ Z).toReal =
              (stabilityMass σ X).toReal +
                ‖σ.charge (GY.factor iHead)‖ := by
          simpa [GZ, iHead, oct] using
            stabilityMass_toReal_appendFactor σ GX oct.triangle oct.mem
              (Iso.refl _) (Iso.refl _) (GY.φ iHead)
              (GY.semistable iHead) hsepHead
        have hsepTail :
            ∀ i : Fin Gtail.n, ∀ j : Fin GZ.n, Gtail.φ i < GZ.φ j := by
          intro i j
          obtain ⟨k, hkval, hkφ⟩ := hφTail i
          change Gtail.φ i <
            (GX.appendFactor C oct.triangle oct.mem
              (Iso.refl _) (Iso.refl _) (GY.φ iHead)
              (GY.semistable iHead) hsepHead).φ j
          simp only [HNFiltration.appendFactor]
          split_ifs with hj
          · rw [hkφ]
            exact hsep k ⟨j.val, hj⟩
          · rw [hkφ]
            exact GY.hφ (show iHead < k by
              apply Fin.mk_lt_mk.mpr
              omega)
        have hmassE := ih GZ Gtail (by rw [hnTail]; omega)
          fZE (g ≫ b) hYZ hZE hsepTail
        change (stabilityMass σ E).toReal =
          (stabilityMass σ Z).toReal +
            (stabilityMass σ Ytail).toReal at hmassE
        linarith

/-- Intrinsic cutoff form of exact mass splitting.  If the left endpoint has
all HN phases strictly above `t` and the right endpoint has all phases at
most `t`, the middle mass is the sum of the endpoint masses. -/
theorem stabilityMass_toReal_triangle_eq_add_of_gtProp_leProp
    (σ : StabilityCondition.WithClassMap C v)
    {X E Y : C} (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang C) (t : ℝ)
    (hX : σ.slicing.gtProp C t X) (hY : σ.slicing.leProp C t Y) :
    (stabilityMass σ E).toReal =
      (stabilityMass σ X).toReal + (stabilityMass σ Y).toReal := by
  rcases hX with hXzero | ⟨GX, hGX, hXgt⟩
  · haveI : IsIso g := (Triangle.isZero₁_iff_isIso₂ _ hT).mp hXzero
    rw [stabilityMass_congr σ (asIso g)]
    rw [show stabilityMass σ X = 0 from
      (stabilityMass_eq_zero_iff σ X).2 hXzero]
    simp
  · rcases hY with hYzero | ⟨GY, hGY, hYle⟩
    · haveI : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hYzero
      rw [stabilityMass_congr σ (asIso f)]
      rw [show stabilityMass σ Y = 0 from
        (stabilityMass_eq_zero_iff σ Y).2 hYzero]
      simp
    · apply stabilityMass_toReal_triangle_eq_add_of_hn_separated
        σ GX GY f g h hT
      intro i j
      calc
        GY.φ i ≤ GY.φ ⟨0, hGY⟩ :=
          GY.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        _ ≤ t := by
          simpa only [CategoryTheory.Triangulated.HNFiltration.phiPlus] using hYle
        _ < GX.φ ⟨GX.n - 1, by lia⟩ := by
          simpa only [CategoryTheory.Triangulated.HNFiltration.phiMinus] using hXgt
        _ ≤ GX.φ j :=
          GX.hφ.antitone (Fin.mk_le_mk.mpr (by lia))

/-- On the amplitude window with phases in `(0, 2]`, mass is the sum of the
masses of the only two possibly nonzero heart-cohomology objects. -/
theorem stabilityMass_toReal_eq_heartCoh_negOne_add_zero
    (σ : StabilityCondition.WithClassMap C v) (X : C)
    (hgt : σ.slicing.gtProp C 0 X) (hle : σ.slicing.leProp C 2 X) :
    (stabilityMass σ X).toReal =
      (stabilityMass σ
        (CategoryTheory.Triangulated.Tilting.originalHeartCoh
          σ.slicing.toTStructure (-1) X).obj).toReal +
      (stabilityMass σ
        (CategoryTheory.Triangulated.Tilting.originalHeartCoh
          σ.slicing.toTStructure 0 X).obj).toReal := by
  let t := σ.slicing.toTStructure
  letI hXLE : t.IsLE X 0 := by
    refine ⟨?_⟩
    dsimp [t, Slicing.toTStructure]
    simpa using hgt
  letI hXGE : t.IsGE X (-1) := by
    refine ⟨?_⟩
    dsimp [t, Slicing.toTStructure]
    norm_num
    exact hle
  let T := (t.triangleLTGE 0).obj X
  have hT : T ∈ distTriang C := t.triangleLTGE_distinguished 0 X
  letI hT₁LE : t.IsLE T.obj₁ (-1) := by
    dsimp [T]
    exact t.isLE_truncLT_obj X 0 (-1) (by lia)
  letI hT₁GE : t.IsGE T.obj₁ (-1) := by
    dsimp [T]
    infer_instance
  letI hT₂LE : t.IsLE T.obj₂ 0 := by
    dsimp [T]
    exact hXLE
  letI hT₂GE : t.IsGE T.obj₂ (-1) := by
    dsimp [T]
    exact hXGE
  have hKLE : t.IsLE (T.obj₁⟦(-1 : ℤ)⟧) 0 :=
    t.isLE_shift (X := T.obj₁) (-1) (-1) 0 (by lia)
  have hKGE : t.IsGE (T.obj₁⟦(-1 : ℤ)⟧) 0 :=
    t.isGE_shift (X := T.obj₁) (-1) (-1) 0 (by lia)
  have hKheart : t.heart (T.obj₁⟦(-1 : ℤ)⟧) :=
    (t.mem_heart_iff _).2 ⟨hKLE, hKGE⟩
  let K : t.heart.FullSubcategory := ⟨T.obj₁⟦(-1 : ℤ)⟧, hKheart⟩
  have hQLE : t.IsLE T.obj₃ 0 := by
    dsimp [T]
    infer_instance
  have hQGE : t.IsGE T.obj₃ 0 := by
    dsimp [T]
    infer_instance
  have hQheart : t.heart T.obj₃ := (t.mem_heart_iff _).2 ⟨hQLE, hQGE⟩
  let Q : t.heart.FullSubcategory := ⟨T.obj₃, hQheart⟩
  let eK : K.obj⟦(1 : ℤ)⟧ ≅ T.obj₁ := shiftNegShift T.obj₁ (1 : ℤ)
  let TK : Triangle C := Triangle.mk
    (eK.hom ≫ T.mor₁) T.mor₂ (T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map eK.inv)
  have hTK : TK ∈ distTriang C := by
    refine isomorphic_distinguished _ hT TK ?_
    exact (Triangle.isoMk T TK eK.symm (Iso.refl _) (Iso.refl _)
      (by simp [TK]) (by simp [TK]) (by simp [TK])).symm
  have hKgt : σ.slicing.gtProp C 1 TK.obj₁ := by
    have hK0 : σ.slicing.gtProp C 0 K.obj :=
      (σ.slicing.toTStructure_heart_iff C K.obj).mp K.property |>.1
    simpa [TK, K] using σ.slicing.gtProp_shift C 0 K.obj 1 hK0
  have hQle : σ.slicing.leProp C 1 TK.obj₃ :=
    (σ.slicing.toTStructure_heart_iff C Q.obj).mp Q.property |>.2
  have hmass := stabilityMass_toReal_triangle_eq_add_of_gtProp_leProp
    σ TK.mor₁ TK.mor₂ TK.mor₃ hTK 1 hKgt hQle
  have eNeg := CategoryTheory.Triangulated.Tilting.originalHeartCohNegOneIsoOfAmplitude
    t K.property Q.property hTK
  have eZero := CategoryTheory.Triangulated.Tilting.originalHeartCohZeroIsoOfAmplitude
    t K.property Q.property hTK
  change (stabilityMass σ X).toReal =
    (stabilityMass σ (K.obj⟦(1 : ℤ)⟧)).toReal +
      (stabilityMass σ Q.obj).toReal at hmass
  rw [stabilityMass_shift_one] at hmass
  have hNegMass := stabilityMass_congr σ ((t.heart).ι.mapIso eNeg)
  have hZeroMass := stabilityMass_congr σ ((t.heart).ι.mapIso eZero)
  change stabilityMass σ
      (CategoryTheory.Triangulated.Tilting.originalHeartCoh t (-1) X).obj =
    stabilityMass σ K.obj at hNegMass
  change stabilityMass σ
      (CategoryTheory.Triangulated.Tilting.originalHeartCoh t 0 X).obj =
    stabilityMass σ Q.obj at hZeroMass
  rw [hNegMass, hZeroMass]
  exact hmass

omit [IsTriangulated C] in
/-- The charge of the middle object in a distinguished triangle is the sum
of the endpoint charges. -/
theorem StabilityCondition.WithClassMap.charge_triangle
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C) :
    σ.charge T.obj₂ = σ.charge T.obj₁ + σ.charge T.obj₃ := by
  simp only [PreStabilityCondition.WithClassMap.charge_def,
    classOf_triangle C v T hT, map_add]

/-- Mass is subadditive along a distinguished triangle whose middle object is
semistable. -/
theorem stabilityMass_triangle_le_of_obj₂_semistable
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C) {φ : ℝ} (h₂ : σ.slicing.P φ T.obj₂) :
    (stabilityMass σ T.obj₂).toReal ≤
      (stabilityMass σ T.obj₁).toReal +
        (stabilityMass σ T.obj₃).toReal := by
  rw [stabilityMass_toReal_eq_norm_charge σ h₂,
    σ.charge_triangle T hT]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_charge_le_stabilityMass_toReal σ T.obj₁)
      (norm_charge_le_stabilityMass_toReal σ T.obj₃))

/-- Mass is subadditive when both endpoints of a distinguished triangle are
semistable of the same phase. -/
theorem stabilityMass_triangle_le_of_same_phase
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C) (φ : ℝ)
    (h₁ : σ.slicing.P φ T.obj₁) (h₃ : σ.slicing.P φ T.obj₃) :
    (stabilityMass σ T.obj₂).toReal ≤
      (stabilityMass σ T.obj₁).toReal +
        (stabilityMass σ T.obj₃).toReal := by
  exact stabilityMass_triangle_le_of_obj₂_semistable σ T hT
    (σ.slicing.semistable_of_triangle C φ h₁ h₃ hT)

/-- Mass is exactly additive when both endpoints of a distinguished triangle
lie in one semistable slice.  The middle object is in the same slice by
extension closure, and all three charges lie on the same ray. -/
theorem stabilityMass_toReal_triangle_eq_add_of_same_phase
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C) (φ : ℝ)
    (h₁ : σ.slicing.P φ T.obj₁) (h₃ : σ.slicing.P φ T.obj₃) :
    (stabilityMass σ T.obj₂).toReal =
      (stabilityMass σ T.obj₁).toReal +
        (stabilityMass σ T.obj₃).toReal := by
  have h₂ := σ.slicing.semistable_of_triangle C φ h₁ h₃ hT
  by_cases h₁z : IsZero T.obj₁
  · haveI : IsIso T.mor₂ := (Triangle.isZero₁_iff_isIso₂ T hT).mp h₁z
    rw [stabilityMass_congr σ (asIso T.mor₂)]
    rw [show stabilityMass σ T.obj₁ = 0 from
      (stabilityMass_eq_zero_iff σ T.obj₁).2 h₁z]
    simp
  · by_cases h₃z : IsZero T.obj₃
    · haveI : IsIso T.mor₁ := (Triangle.isZero₃_iff_isIso₁ T hT).mp h₃z
      rw [stabilityMass_congr σ (asIso T.mor₁)]
      rw [show stabilityMass σ T.obj₃ = 0 from
        (stabilityMass_eq_zero_iff σ T.obj₃).2 h₃z]
      simp
    · obtain ⟨m₁, hm₁, hZ₁⟩ := σ.compat φ T.obj₁ h₁ h₁z
      obtain ⟨m₃, hm₃, hZ₃⟩ := σ.compat φ T.obj₃ h₃ h₃z
      rw [stabilityMass_toReal_eq_norm_charge σ h₂,
        stabilityMass_toReal_eq_norm_charge σ h₁,
        stabilityMass_toReal_eq_norm_charge σ h₃,
        σ.charge_triangle T hT, hZ₁, hZ₃, ← add_mul]
      rw [norm_mul, norm_mul, norm_mul]
      rw [show ‖(m₁ : ℂ) + (m₃ : ℂ)‖ = m₁ + m₃ by
        simpa [abs_of_pos (add_pos hm₁ hm₃)] using
          Complex.norm_real (m₁ + m₃)]
      simp only [Complex.norm_real, Real.norm_of_nonneg hm₁.le,
        Real.norm_of_nonneg hm₃.le]
      ring

/-- At the upper boundary of the canonical heart, a semistable left endpoint
can be prepended to an arbitrary heart object without increasing mass beyond
the sum of the endpoint masses.

If the right endpoint has no phase-one HN factor, the two endpoint
filtrations are strictly separated.  Otherwise its unique phase-one head is
first combined with the left endpoint; that extension remains in `P(1)`, and
the remaining HN tail is strictly lower.  This is the precise mass comparison
behind the "easy to check" phase-one extension step in Ikeda's proof of
Proposition 3.3. -/
theorem stabilityMass_triangle_le_of_obj₁_phase_one_of_obj₃_le_one
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C)
    (h₁ : σ.slicing.P 1 T.obj₁)
    (h₃ : σ.slicing.leProp C 1 T.obj₃) :
    (stabilityMass σ T.obj₂).toReal ≤
      (stabilityMass σ T.obj₁).toReal +
        (stabilityMass σ T.obj₃).toReal := by
  rcases h₃ with hYzero | ⟨GY, hGYpos, hGYle⟩
  · haveI : IsIso T.mor₁ :=
      (Triangle.isZero₃_iff_isIso₁ T hT).mp hYzero
    rw [stabilityMass_congr σ (asIso T.mor₁)]
    rw [show stabilityMass σ T.obj₃ = 0 from
      (stabilityMass_eq_zero_iff σ T.obj₃).2 hYzero]
    simp
  · let iHead : Fin GY.n := ⟨0, hGYpos⟩
    have htop_le : GY.φ iHead ≤ 1 := by
      simpa only [CategoryTheory.Triangulated.HNFiltration.phiPlus] using hGYle
    by_cases htop : GY.φ iHead = 1
    · obtain ⟨Ytail, Gtail, a, b, c, hHead, hmassY, hnTail, hφTail⟩ :=
        CategoryTheory.Triangulated.HNFiltration.exists_headTail_mass σ GY hGYpos
      obtain ⟨Z, fZE, hYZ, hZE⟩ :=
        distinguished_cocone_triangle₁ (T.mor₂ ≫ b)
      let oct := Triangulated.someOctahedron'
        (show T.mor₂ ≫ b = T.mor₂ ≫ b by rfl) hT hHead hZE
      have hHeadP : σ.slicing.P 1 (GY.factor iHead) := by
        simpa [htop] using GY.semistable iHead
      have hZP : σ.slicing.P 1 Z := by
        exact σ.slicing.semistable_of_triangle C 1 h₁ hHeadP oct.mem
      have hmassZ :
          (stabilityMass σ Z).toReal ≤
            (stabilityMass σ T.obj₁).toReal +
              (stabilityMass σ (GY.factor iHead)).toReal := by
        simpa [oct] using stabilityMass_triangle_le_of_same_phase
          σ oct.triangle oct.mem 1 h₁ hHeadP
      let GZ := HNFiltration.single C Z 1 hZP
      have hsep : ∀ i : Fin Gtail.n, ∀ j : Fin GZ.n,
          Gtail.φ i < GZ.φ j := by
        intro i j
        obtain ⟨k, hkval, hkφ⟩ := hφTail i
        have hkpos : iHead < k := by
          apply Fin.mk_lt_mk.mpr
          omega
        rw [hkφ]
        rw [show GZ.φ j = 1 by rfl, ← htop]
        exact GY.hφ hkpos
      have hmassE := stabilityMass_toReal_triangle_eq_add_of_hn_separated
        σ GZ Gtail fZE (T.mor₂ ≫ b) hYZ hZE hsep
      have hHeadMass := stabilityMass_toReal_eq_norm_charge σ hHeadP
      change (stabilityMass σ T.obj₂).toReal =
        (stabilityMass σ Z).toReal +
          (stabilityMass σ Ytail).toReal at hmassE
      change (stabilityMass σ T.obj₃).toReal =
        ‖σ.charge (GY.factor iHead)‖ +
          (stabilityMass σ Ytail).toReal at hmassY
      linarith
    · have htop_lt : GY.φ iHead < 1 := lt_of_le_of_ne htop_le htop
      let GX := HNFiltration.single C T.obj₁ 1 h₁
      have hsep : ∀ i : Fin GY.n, ∀ j : Fin GX.n,
          GY.φ i < GX.φ j := by
        intro i j
        have hi : GY.φ i ≤ GY.φ iHead :=
          GY.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        change GY.φ i < 1
        exact hi.trans_lt htop_lt
      exact le_of_eq (stabilityMass_toReal_triangle_eq_add_of_hn_separated
        σ GX GY T.mor₁ T.mor₂ T.mor₃ hT hsep)

/-- The first major mass-triangle milestone, in its phase-one boundary-heart
form.  For a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` in the
canonical heart with `C ∈ P(1)`, the mass of `A` is at most the combined
mass of `B` and `C`.

This is a named proof target, not an installed premise. -/
def StabilityMassBoundaryHeartInequality : Prop :=
  ∀ (σ : StabilityCondition.WithClassMap C v)
    (S : ShortComplex σ.slicing.toTStructure.heart.FullSubcategory),
    S.ShortExact → σ.slicing.P 1 S.X₃.obj →
      (stabilityMass σ S.X₁.obj).toReal ≤
        (stabilityMass σ S.X₂.obj).toReal +
          (stabilityMass σ S.X₃.obj).toReal

/-- The second paper-level mass-triangle milestone: subadditivity for a
distinguished triangle whose first object is semistable. -/
def StabilityMassSemistableLeftTriangleInequality : Prop :=
  ∀ (σ : StabilityCondition.WithClassMap C v) (T : Triangle C),
    T ∈ distTriang C →
    ∀ (φ : ℝ), σ.slicing.P φ T.obj₁ →
      (stabilityMass σ T.obj₂).toReal ≤
        (stabilityMass σ T.obj₁).toReal +
          (stabilityMass σ T.obj₃).toReal

/-- The arbitrary-left octahedral milestone.  Once the triangle inequality is
known for semistable first objects, split an HN filtration of the first object
into its head and tail.  The octahedron produces one semistable-left triangle
and a shorter arbitrary-left triangle, so induction proves the unrestricted
statement. -/
theorem stabilityMassTriangleInequality_of_semistable_obj₁
    (hsemistable :
      StabilityMassSemistableLeftTriangleInequality (C := C) (v := v)) :
    StabilityMassTriangleInequality (C := C) (v := v) := by
  intro σ T hT
  obtain ⟨F⟩ := σ.slicing.hn_exists T.obj₁
  suffices hmain :
      ∀ (m : ℕ) (U : Triangle C), U ∈ distTriang C →
        ∀ G : HNFiltration C σ.slicing.P U.obj₁, G.n ≤ m →
          (stabilityMass σ U.obj₂).toReal ≤
            (stabilityMass σ U.obj₁).toReal +
              (stabilityMass σ U.obj₃).toReal by
    exact hmain F.n T hT F le_rfl
  intro m
  induction m with
  | zero =>
      intro U hU G hG
      have hn : G.n = 0 := by omega
      have hzero : IsZero U.obj₁ := G.isZero_of_length_zero hn
      haveI : IsIso U.mor₂ := (Triangle.isZero₁_iff_isIso₂ U hU).mp hzero
      rw [stabilityMass_congr σ (asIso U.mor₂)]
      simp [show stabilityMass σ U.obj₁ = 0 from
        (stabilityMass_eq_zero_iff σ U.obj₁).2 hzero]
  | succ m ih =>
      intro U hU G hG
      by_cases hn0 : G.n = 0
      · have hzero : IsZero U.obj₁ := G.isZero_of_length_zero hn0
        haveI : IsIso U.mor₂ := (Triangle.isZero₁_iff_isIso₂ U hU).mp hzero
        rw [stabilityMass_congr σ (asIso U.mor₂)]
        simp [show stabilityMass σ U.obj₁ = 0 from
          (stabilityMass_eq_zero_iff σ U.obj₁).2 hzero]
      · have hn : 0 < G.n := Nat.pos_of_ne_zero hn0
        obtain ⟨Y, Gtail, f, _g, _δ, hhead, hmass, hnTail, _hφ⟩ :=
          G.exists_headTail_mass σ hn
        obtain ⟨Z, v₁₃, w₁₃, h₁₃⟩ :=
          distinguished_cocone_triangle (f ≫ U.mor₁)
        let oct := Triangulated.someOctahedron rfl hhead hU h₁₃
        have hfirst := hsemistable σ
          (Triangle.mk (f ≫ U.mor₁) v₁₃ w₁₃) h₁₃
          (G.φ ⟨0, hn⟩) (G.semistable ⟨0, hn⟩)
        have hheadMass :
            (stabilityMass σ (G.factor ⟨0, hn⟩)).toReal =
              ‖σ.charge (G.factor ⟨0, hn⟩)‖ :=
          stabilityMass_toReal_eq_norm_charge σ (G.semistable ⟨0, hn⟩)
        change (stabilityMass σ U.obj₂).toReal ≤
          (stabilityMass σ (G.factor ⟨0, hn⟩)).toReal +
            (stabilityMass σ Z).toReal at hfirst
        rw [hheadMass] at hfirst
        have htail :
            (stabilityMass σ Z).toReal ≤
              (stabilityMass σ Y).toReal +
                (stabilityMass σ U.obj₃).toReal := by
          simpa [oct] using ih oct.triangle oct.mem Gtail (by
            rw [hnTail]
            omega)
        linarith

/-- The first remaining polygonal milestone: mass subadditivity for every
short exact sequence in the canonical heart `P((0, 1])`. -/
def StabilityMassHeartShortExactInequality : Prop :=
  ∀ (σ : StabilityCondition.WithClassMap C v)
    (S : ShortComplex σ.slicing.toTStructure.heart.FullSubcategory),
    S.ShortExact →
      (stabilityMass σ S.X₂.obj).toReal ≤
        (stabilityMass σ S.X₁.obj).toReal +
          (stabilityMass σ S.X₃.obj).toReal

/-- A short exact sequence in the canonical heart is induced by a
distinguished triangle on its underlying ambient objects. -/
theorem heartShortExact_exists_distinguished_triangle
    (σ : StabilityCondition.WithClassMap C v)
    (S : ShortComplex σ.slicing.toTStructure.heart.FullSubcategory)
    (hS : S.ShortExact) :
    ∃ δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧,
      Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : IsNormalMonoCategory t.heart.FullSubcategory :=
    Abelian.toIsNormalMonoCategory
  letI : IsNormalEpiCategory t.heart.FullSubcategory :=
    Abelian.toIsNormalEpiCategory
  letI : Balanced t.heart.FullSubcategory := by infer_instance
  haveI := hS.mono_f
  haveI := hS.epi_g
  exact TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) t S.f S.g S.zero (fun {W} α hα ↦ by
      have hker : IsLimit (KernelFork.ofι S.f S.zero) := hS.fIsKernel
      exact ⟨hker.lift (KernelFork.ofι α hα),
        hker.fac _ WalkingParallelPair.zero⟩)

/-- In a short exact sequence in the canonical heart, if the middle object
lies on the phase-one boundary ray, then both endpoint objects do as well.
This is the boundary-specific kernel/image closure used in the six-term
cohomology argument; it does not assert the false general closure of
`P(φ)` under arbitrary heart subobjects. -/
theorem phaseOne_endpoints_of_heart_shortExact
    (σ : StabilityCondition.WithClassMap C v)
    (S : ShortComplex σ.slicing.toTStructure.heart.FullSubcategory)
    (hS : S.ShortExact) (h₂ : σ.slicing.P 1 S.X₂.obj) :
    σ.slicing.P 1 S.X₁.obj ∧ σ.slicing.P 1 S.X₃.obj := by
  let t := σ.slicing.toTStructure
  let Z := σ.observableStabilityFunctionOnHeart
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  by_cases h₁ : IsZero S.X₁
  · have h₁obj := (t.heart).ι.map_isZero h₁
    haveI : IsIso S.g := hS.isIso_g_iff.mpr h₁
    exact ⟨σ.slicing.zero_mem_of_isZero C 1 _ h₁obj,
      (σ.slicing.P 1).prop_of_iso ((t.heart).ι.mapIso (asIso S.g)) h₂⟩
  · by_cases h₃ : IsZero S.X₃
    · have h₃obj := (t.heart).ι.map_isZero h₃
      haveI : IsIso S.f := hS.isIso_f_iff.mpr h₃
      exact ⟨(σ.slicing.P 1).prop_of_iso
          ((t.heart).ι.mapIso (asIso S.f)).symm h₂,
        σ.slicing.zero_mem_of_isZero C 1 _ h₃obj⟩
    · have h₁obj : ¬IsZero S.X₁.obj := fun hz ↦ h₁ <|
        ObjectProperty.FullSubcategory.isZero_of_obj_isZero
          (C := C) (P := t.heart) (X := S.X₁) hz
      have h₃obj : ¬IsZero S.X₃.obj := fun hz ↦ h₃ <|
        ObjectProperty.FullSubcategory.isZero_of_obj_isZero
          (C := C) (P := t.heart) (X := S.X₃) hz
      have h₂obj : ¬IsZero S.X₂.obj := by
        intro hz
        have hz' := ObjectProperty.FullSubcategory.isZero_of_obj_isZero
          (C := C) (P := t.heart) (X := S.X₂) hz
        haveI := hS.mono_f
        exact h₁ (IsZero.of_mono S.f hz')
      obtain ⟨m, hm, hcharge⟩ := σ.compat 1 S.X₂.obj h₂ h₂obj
      have him₂ : (Z.charge S.X₂).im = 0 := by
        change (σ.charge S.X₂.obj).im = 0
        rw [hcharge]
        simp [Complex.exp_mul_I]
      have hadd := Z.additive S hS
      have himadd : (Z.charge S.X₂).im =
          (Z.charge S.X₁).im + (Z.charge S.X₃).im := by
        simpa using congrArg Complex.im hadd
      have him₁_nonneg : 0 ≤ (Z.charge S.X₁).im := by
        rcases Z.nonzero_mem S.X₁ h₁ with h | ⟨h, -⟩
        · exact h.le
        · exact h.ge
      have him₃_nonneg : 0 ≤ (Z.charge S.X₃).im := by
        rcases Z.nonzero_mem S.X₃ h₃ with h | ⟨h, -⟩
        · exact h.le
        · exact h.ge
      have him₁ : (Z.charge S.X₁).im = 0 := by linarith
      have him₃ : (Z.charge S.X₃).im = 0 := by linarith
      have hre₁ : (Z.charge S.X₁).re < 0 := by
        rcases Z.nonzero_mem S.X₁ h₁ with h | h
        · exfalso
          simpa [him₁] using h
        · exact h.2
      have hre₃ : (Z.charge S.X₃).re < 0 := by
        rcases Z.nonzero_mem S.X₃ h₃ with h | h
        · exfalso
          simpa [him₃] using h
        · exact h.2
      have hphase₁ : Z.phase S.X₁ = 1 := by
        rw [StabilityFunction.phase]
        have hz : Z.charge S.X₁ = ((Z.charge S.X₁).re : ℂ) :=
          Complex.ext rfl (by simpa using him₁)
        rw [hz, Complex.arg_ofReal_of_neg hre₁]
        field_simp [Real.pi_ne_zero]
      have hphase₃ : Z.phase S.X₃ = 1 := by
        rw [StabilityFunction.phase]
        have hz : Z.charge S.X₃ = ((Z.charge S.X₃).re : ℂ) :=
          Complex.ext rfl (by simpa using him₃)
        rw [hz, Complex.arg_ofReal_of_neg hre₃]
        field_simp [Real.pi_ne_zero]
      have hss₁ : Z.IsSemistable S.X₁ := ⟨h₁, fun B _ ↦ by
        rw [hphase₁]
        exact Z.phase_le_one B⟩
      have hss₃ : Z.IsSemistable S.X₃ := ⟨h₃, fun B _ ↦ by
        rw [hphase₃]
        exact Z.phase_le_one B⟩
      have hP₁ := σ.mem_slicing_of_heart_isSemistable S.X₁ hss₁
      have hP₃ := σ.mem_slicing_of_heart_isSemistable S.X₃ hss₃
      rw [hphase₁] at hP₁
      rw [hphase₃] at hP₃
      exact ⟨hP₁, hP₃⟩

/-- An abelian HN filtration in the canonical heart is also an ambient HN
filtration after replacing each short exact successive quotient by its
distinguished triangle.  Consequently its factor-norm mass is exactly the
ambient `stabilityMass`. -/
theorem AbelianHNFiltration.mass_eq_stabilityMass_toReal
    (σ : StabilityCondition.WithClassMap C v)
    {E : σ.slicing.toTStructure.heart.FullSubcategory}
    (F : @AbelianHNFiltration _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E) :
    @AbelianHNFiltration.mass _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E F =
        (stabilityMass σ E.obj).toReal := by
  let t := σ.slicing.toTStructure
  let Z := σ.observableStabilityFunctionOnHeart
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let fH (i : Fin F.n) :
      (F.chain i.castSucc : t.heart.FullSubcategory) ⟶
        (F.chain i.succ : t.heart.FullSubcategory) :=
    Subobject.ofLE (F.chain i.castSucc) (F.chain i.succ)
      (le_of_lt (F.chain_strictMono i.castSucc_lt_succ))
  haveI hmono (i : Fin F.n) : Mono (fH i) := by
    dsimp [fH]
    infer_instance
  let S (i : Fin F.n) : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk (fH i) (cokernel.π (fH i)) (cokernel.condition (fH i))
  have hS (i : Fin F.n) : (S i).ShortExact := by
    exact StabilityFunction.shortExact_of_mono (fH i)
  let δ (i : Fin F.n) :
      (cokernel (fH i)).obj ⟶ (F.chain i.castSucc : t.heart.FullSubcategory).obj⟦(1 : ℤ)⟧ :=
    Classical.choose (heartShortExact_exists_distinguished_triangle σ (S i) (hS i))
  have hδ (i : Fin F.n) :
      Triangle.mk (fH i).hom (cokernel.π (fH i)).hom (δ i) ∈ distTriang C := by
    exact Classical.choose_spec
      (heartShortExact_exists_distinguished_triangle σ (S i) (hS i))
  let objFn : Fin (F.n + 1) → C := fun j ↦ (F.chain j : t.heart.FullSubcategory).obj
  let mapSuccFn : ∀ i : Fin F.n, objFn i.castSucc ⟶ objFn i.succ :=
    fun i ↦ (fH i).hom
  let T (i : Fin F.n) : Triangle C :=
    Triangle.mk (fH i).hom (cokernel.π (fH i)).hom (δ i)
  let G : HNFiltration C σ.slicing.P E.obj :=
    { n := F.n
      chain := ComposableArrows.mkOfObjOfMapSucc objFn mapSuccFn
      triangle := T
      triangle_dist := fun i ↦ hδ i
      triangle_obj₁ := fun i ↦ ⟨eqToIso (by
        simp only [T, ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj,
          objFn]
        rfl)⟩
      triangle_obj₂ := fun i ↦ ⟨eqToIso (by
        simp only [T, ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj,
          objFn]
        rfl)⟩
      base_isZero := by
        change IsZero (objFn 0)
        have hzero : IsZero (F.chain 0 : t.heart.FullSubcategory) :=
          (StabilityFunction.subobject_isZero_iff_eq_bot (F.chain 0)).2 F.chain_bot
        exact (t.heart).ι.map_isZero hzero
      top_iso := by
        have htop : F.chain (Fin.last F.n) = ⊤ := F.chain_top
        let eEq : (F.chain (Fin.last F.n) : t.heart.FullSubcategory) ≅
            ((⊤ : Subobject E) : t.heart.FullSubcategory) :=
          eqToIso (congrArg (fun S : Subobject E ↦
            (S : t.heart.FullSubcategory)) htop)
        let eTop : (F.chain (Fin.last F.n) : t.heart.FullSubcategory) ≅ E :=
          eEq.trans (asIso (⊤ : Subobject E).arrow)
        exact ⟨(t.heart).ι.mapIso eTop⟩
      φ := F.phase
      hφ := F.phase_strictAnti
      semistable := fun i ↦ by
        have hP := σ.mem_slicing_of_heart_isSemistable
          (cokernel (fH i)) (by simpa [Z, fH] using F.factor_semistable i)
        rw [show Z.phase (cokernel (fH i)) = F.phase i by
          simpa [Z, fH] using F.factor_phase i] at hP
        exact hP }
  rw [stabilityMass_toReal_eq_sum σ G]
  unfold AbelianHNFiltration.mass
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- The phase-one boundary-heart mass inequality.  The nonzero case is the
boundary-cut comparison for abelian HN polygons, transported to ambient mass
by `AbelianHNFiltration.mass_eq_stabilityMass_toReal`; the zero source case is
handled directly. -/
theorem stabilityMassBoundaryHeartInequality :
    StabilityMassBoundaryHeartInequality (C := C) (v := v) := by
  intro σ S hS h₃
  let t := σ.slicing.toTStructure
  let Z := σ.observableStabilityFunctionOnHeart
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  by_cases h₁ : IsZero S.X₁
  · have h₁obj : IsZero S.X₁.obj := (t.heart).ι.map_isZero h₁
    rw [show stabilityMass σ S.X₁.obj = 0 from
      (stabilityMass_eq_zero_iff σ S.X₁.obj).2 h₁obj]
    positivity
  · haveI := hS.mono_f
    have h₂ : ¬IsZero S.X₂ := by
      intro h₂
      exact h₁ (IsZero.of_mono S.f h₂)
    obtain ⟨F⟩ := σ.observableStabilityFunctionOnHeart_hasHN S.X₁ h₁
    obtain ⟨G⟩ := σ.observableStabilityFunctionOnHeart_hasHN S.X₂ h₂
    have hmass := AbelianHNFiltration.mass_le_add_norm_of_shortExact
      S hS F G σ.observableStabilityFunctionOnHeart_hasHN
    calc
      (stabilityMass σ S.X₁.obj).toReal =
          @AbelianHNFiltration.mass _ _
            ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
            σ.observableStabilityFunctionOnHeart S.X₁ F :=
        (AbelianHNFiltration.mass_eq_stabilityMass_toReal σ F).symm
      _ ≤ @AbelianHNFiltration.mass _ _
            ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
            σ.observableStabilityFunctionOnHeart S.X₂ G + ‖Z.charge S.X₃‖ := hmass
      _ = (stabilityMass σ S.X₂.obj).toReal +
          (stabilityMass σ S.X₃.obj).toReal := by
        rw [AbelianHNFiltration.mass_eq_stabilityMass_toReal σ G,
          stabilityMass_toReal_eq_norm_charge σ h₃]
        rfl

set_option maxHeartbeats 3000000
/-- The six-term comparison at the level of the shifted homological functor.
Keeping this categorical construction separate from the canonical
`heartCoh` identifications substantially reduces elaboration cost for the
public cohomology comparison below. -/
theorem stabilityMass_H0FunctorShift_negOne_zero_triangle_le_of_obj₁_phase_one
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C)
    (h₁ : σ.slicing.P 1 T.obj₁) :
    (stabilityMass σ
      (((CategoryTheory.Triangulated.Tilting.originalHeartCohFunctor
        σ.slicing.toTStructure 0).shift (-1)).obj T.obj₂).obj).toReal +
      (stabilityMass σ
        (((CategoryTheory.Triangulated.Tilting.originalHeartCohFunctor
          σ.slicing.toTStructure 0).shift (0 : ℤ)).obj T.obj₂).obj).toReal ≤
      (stabilityMass σ T.obj₁).toReal +
        ((stabilityMass σ
          (((CategoryTheory.Triangulated.Tilting.originalHeartCohFunctor
            σ.slicing.toTStructure 0).shift (-1)).obj T.obj₃).obj).toReal +
          (stabilityMass σ
            (((CategoryTheory.Triangulated.Tilting.originalHeartCohFunctor
              σ.slicing.toTStructure 0).shift (0 : ℤ)).obj T.obj₃).obj).toReal) := by
  let t := σ.slicing.toTStructure
  let H := CategoryTheory.Triangulated.Tilting.originalHeartCohFunctor t 0
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : Functor.IsHomological H := by
    dsimp [H]
    infer_instance
  have hAheart : t.heart T.obj₁ := by
    dsimp [t]
    rw [σ.slicing.toTStructure_heart_iff C]
    exact ⟨σ.slicing.gtProp_of_semistable C h₁ (by norm_num),
      σ.slicing.leProp_of_semistable C h₁ le_rfl⟩
  let AH : t.heart.FullSubcategory := ⟨T.obj₁, hAheart⟩
  let Em : t.heart.FullSubcategory := (H.shift (-1)).obj T.obj₂
  let Fm : t.heart.FullSubcategory := (H.shift (-1)).obj T.obj₃
  let A0 : t.heart.FullSubcategory := (H.shift (0 : ℤ)).obj T.obj₁
  let E0 : t.heart.FullSubcategory := (H.shift (0 : ℤ)).obj T.obj₂
  let F0 : t.heart.FullSubcategory := (H.shift (0 : ℤ)).obj T.obj₃
  let gNeg : Em ⟶ Fm := (H.shift (-1)).map T.mor₂
  let δNeg : Fm ⟶ A0 := H.homologySequenceδ T (-1) (0 : ℤ) (by omega)
  let f0 : A0 ⟶ E0 := (H.shift (0 : ℤ)).map T.mor₁
  let g0 : E0 ⟶ F0 := (H.shift (0 : ℤ)).map T.mor₂

  let eA0 : A0 ≅ AH :=
    CategoryTheory.Triangulated.Tilting.originalHeartCohShiftIso t 0 T.obj₁ ≪≫
      CategoryTheory.Triangulated.Tilting.originalHeartCohIsoOfHeart t AH
  have hA0P : σ.slicing.P 1 A0.obj :=
    (σ.slicing.P 1).prop_of_iso ((t.heart).ι.mapIso eA0).symm h₁

  have hAminusZero : IsZero ((H.shift (-1)).obj T.obj₁) := by
    exact CategoryTheory.Triangulated.Tilting.originalHeartCohFunctor_shift_isZero_of_isGE
      t ⟨hAheart.2⟩ (by omega)
  have hfNegZero : (H.shift (-1)).map T.mor₁ = 0 :=
    hAminusZero.eq_of_src _ 0
  letI : Mono gNeg :=
    (H.homologySequence_exact₂ T hT (-1)).mono_g hfNegZero
  have hgNegδ : gNeg ≫ δNeg = 0 := by
    simpa [gNeg, δNeg] using
      H.comp_homologySequenceδ T hT (-1) (0 : ℤ) (by omega)
  let K : t.heart.FullSubcategory := Abelian.image δNeg
  let qNeg : Fm ⟶ K := Abelian.factorThruImage δNeg
  have hgqNeg : gNeg ≫ qNeg = 0 := by
    rw [← cancel_mono (Abelian.image.ι δNeg), Category.assoc,
      Abelian.image.fac, hgNegδ, zero_comp]
  let Sneg : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk gNeg qNeg hgqNeg
  let SnegWide : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk gNeg δNeg hgNegδ
  have hSnegWide : SnegWide.Exact := by
    simpa [SnegWide, gNeg, δNeg] using
      H.homologySequence_exact₃ T hT (-1) (0 : ℤ) (by omega)
  let SnegCoimage : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk gNeg (Abelian.coimage.π δNeg)
      (Abelian.comp_coimage_π_eq_zero hgNegδ)
  have hSnegCoimage : SnegCoimage.Exact := by
    simpa [SnegCoimage, SnegWide] using
      (SnegWide.exact_iff_exact_coimage_π).mp hSnegWide
  have hcoimageImage : Abelian.coimage.π δNeg ≫
      (Abelian.coimageIsoImage δNeg).hom = qNeg := by
    rw [← cancel_mono (Abelian.image.ι δNeg)]
    simp [qNeg]
  let Ψneg : SnegCoimage ⟶ Sneg := ShortComplex.homMk
    (𝟙 _) (𝟙 _) (Abelian.coimageIsoImage δNeg).hom
      (by simp [SnegCoimage, Sneg])
      (by simpa [SnegCoimage, Sneg] using hcoimageImage.symm)
  letI : Epi Ψneg.τ₁ := by
    dsimp [Ψneg]
    infer_instance
  letI : IsIso Ψneg.τ₂ := by
    dsimp [Ψneg]
    infer_instance
  letI : Mono Ψneg.τ₃ := by
    dsimp [Ψneg]
    infer_instance
  have hSnegExact : Sneg.Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono Ψneg).mp hSnegCoimage
  have hSneg : Sneg.ShortExact := by
    exact ShortComplex.ShortExact.mk hSnegExact

  have hf0g0 : f0 ≫ g0 = 0 := by
    simpa [f0, g0] using H.homologySequence_comp T hT (0 : ℤ)
  let I : t.heart.FullSubcategory := Abelian.image f0
  let i0 : I ⟶ E0 := Abelian.image.ι f0
  let S0 : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk i0 g0 (Abelian.image_ι_comp_eq_zero hf0g0)
  let S0wide : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk f0 g0 hf0g0
  have hS0wide : S0wide.Exact := by
    simpa [S0wide, f0, g0] using
      H.homologySequence_exact₂ T hT (0 : ℤ)
  have hS0Exact : S0.Exact := by
    simpa [S0, S0wide, i0] using
      (S0wide.exact_iff_exact_image_ι).mp hS0wide
  have hAoneZero : IsZero ((H.shift (1 : ℤ)).obj T.obj₁) := by
    exact CategoryTheory.Triangulated.Tilting.originalHeartCohFunctor_shift_isZero_of_isLE
      t ⟨hAheart.1⟩ (by omega)
  have hδ0Zero : H.homologySequenceδ T (0 : ℤ) (1 : ℤ) (by omega) = 0 :=
    hAoneZero.eq_of_tgt _ 0
  letI : Epi g0 :=
    (H.homologySequence_exact₃ T hT (0 : ℤ) (1 : ℤ) (by omega)).epi_f hδ0Zero
  have hS0 : S0.ShortExact := by
    exact ShortComplex.ShortExact.mk hS0Exact

  have hδf0 : δNeg ≫ f0 = 0 := by
    simpa [δNeg, f0] using
      H.homologySequenceδ_comp T hT (-1) (0 : ℤ) (by omega)
  let p0 : A0 ⟶ I := by
    simpa only [I] using Abelian.factorThruImage f0
  have hKp0 : Abelian.image.ι δNeg ≫ p0 = 0 := by
    rw [← cancel_mono (Abelian.image.ι f0), Category.assoc]
    dsimp [p0]
    rw [Abelian.image.fac, zero_comp]
    exact Abelian.image_ι_comp_eq_zero hδf0
  letI : Epi p0 := by
    dsimp [p0]
    infer_instance
  let SA : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk (Abelian.image.ι δNeg) p0 hKp0
  let SAwide : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk (Abelian.image.ι δNeg) f0
      (Abelian.image_ι_comp_eq_zero hδf0)
  let Slong : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk δNeg f0 hδf0
  have hSlong : Slong.Exact := by
    simpa [Slong, δNeg, f0] using
      H.homologySequence_exact₁ T hT (-1) (0 : ℤ) (by omega)
  have hSAwide : SAwide.Exact := by
    simpa [SAwide, Slong] using (Slong.exact_iff_exact_image_ι).mp hSlong
  let Φ : SA ⟶ SAwide := ShortComplex.homMk
    (𝟙 _) (𝟙 _) (Abelian.image.ι f0)
      (by simp [SA, SAwide]) (by simp [SA, SAwide, p0])
  letI : Epi Φ.τ₁ := by
    dsimp [Φ]
    infer_instance
  letI : IsIso Φ.τ₂ := by
    dsimp [Φ]
    infer_instance
  letI : Mono Φ.τ₃ := by
    dsimp [Φ]
    infer_instance
  have hSAexact : SA.Exact := by
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono Φ).mpr hSAwide
  have hSA : SA.ShortExact := by
    exact ShortComplex.ShortExact.mk hSAexact

  obtain ⟨δA, hTA⟩ := heartShortExact_exists_distinguished_triangle σ SA hSA
  let TA : Triangle C := Triangle.mk SA.f.hom SA.g.hom δA
  have hKI : σ.slicing.P 1 K.obj ∧ σ.slicing.P 1 I.obj :=
    phaseOne_endpoints_of_heart_shortExact σ SA hSA hA0P

  have hNeg : (stabilityMass σ Em.obj).toReal ≤
      (stabilityMass σ Fm.obj).toReal +
        (stabilityMass σ K.obj).toReal := by
    exact stabilityMassBoundaryHeartInequality σ Sneg hSneg hKI.1
  obtain ⟨δ₀, hT₀⟩ := heartShortExact_exists_distinguished_triangle σ S0 hS0
  let T₀ : Triangle C := Triangle.mk S0.f.hom S0.g.hom δ₀
  have hF0le : σ.slicing.leProp C 1 F0.obj :=
    ((σ.slicing.toTStructure_heart_iff C F0.obj).mp F0.property).2
  have hZero : (stabilityMass σ E0.obj).toReal ≤
      (stabilityMass σ I.obj).toReal +
        (stabilityMass σ F0.obj).toReal := by
    simpa [T₀, S0] using
      stabilityMass_triangle_le_of_obj₁_phase_one_of_obj₃_le_one
        σ T₀ hT₀ hKI.2 hF0le
  have hAeq : (stabilityMass σ A0.obj).toReal =
      (stabilityMass σ K.obj).toReal +
        (stabilityMass σ I.obj).toReal := by
    simpa [TA, SA] using stabilityMass_toReal_triangle_eq_add_of_same_phase
      σ TA hTA 1 hKI.1 hKI.2

  have hA0Mass := stabilityMass_congr σ ((t.heart).ι.mapIso eA0)
  change stabilityMass σ A0.obj = stabilityMass σ T.obj₁ at hA0Mass
  rw [hA0Mass] at hAeq
  change (stabilityMass σ Em.obj).toReal +
      (stabilityMass σ E0.obj).toReal ≤
    (stabilityMass σ T.obj₁).toReal +
      ((stabilityMass σ Fm.obj).toReal +
        (stabilityMass σ F0.obj).toReal)
  linarith only [hNeg, hZero, hAeq]

/-- The six-term cohomology comparison for a phase-one source.  This is the
homological core of the semistable-left argument, stated before the ambient
objects are reassembled from their two nonzero cohomology degrees. -/
theorem stabilityMass_heartCoh_negOne_zero_triangle_le_of_obj₁_phase_one
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C)
    (h₁ : σ.slicing.P 1 T.obj₁) :
    (stabilityMass σ
      (CategoryTheory.Triangulated.Tilting.originalHeartCoh
        σ.slicing.toTStructure (-1) T.obj₂).obj).toReal +
      (stabilityMass σ
        (CategoryTheory.Triangulated.Tilting.originalHeartCoh
          σ.slicing.toTStructure 0 T.obj₂).obj).toReal ≤
      (stabilityMass σ T.obj₁).toReal +
        ((stabilityMass σ
          (CategoryTheory.Triangulated.Tilting.originalHeartCoh
            σ.slicing.toTStructure (-1) T.obj₃).obj).toReal +
          (stabilityMass σ
            (CategoryTheory.Triangulated.Tilting.originalHeartCoh
              σ.slicing.toTStructure 0 T.obj₃).obj).toReal) := by
  let t := σ.slicing.toTStructure
  let H := CategoryTheory.Triangulated.Tilting.originalHeartCohFunctor t 0
  have hshift :=
    stabilityMass_H0FunctorShift_negOne_zero_triangle_le_of_obj₁_phase_one
      σ T hT h₁
  let eEm := CategoryTheory.Triangulated.Tilting.originalHeartCohShiftIso t (-1) T.obj₂
  let eE0 := CategoryTheory.Triangulated.Tilting.originalHeartCohShiftIso t 0 T.obj₂
  let eFm := CategoryTheory.Triangulated.Tilting.originalHeartCohShiftIso t (-1) T.obj₃
  let eF0 := CategoryTheory.Triangulated.Tilting.originalHeartCohShiftIso t 0 T.obj₃
  have hEmMass := stabilityMass_congr σ ((t.heart).ι.mapIso eEm)
  have hE0Mass := stabilityMass_congr σ ((t.heart).ι.mapIso eE0)
  have hFmMass := stabilityMass_congr σ ((t.heart).ι.mapIso eFm)
  have hF0Mass := stabilityMass_congr σ ((t.heart).ι.mapIso eF0)
  change stabilityMass σ (H.shift (-1) |>.obj T.obj₂).obj =
    stabilityMass σ
      (CategoryTheory.Triangulated.Tilting.originalHeartCoh t (-1) T.obj₂).obj at hEmMass
  change stabilityMass σ (H.shift (0 : ℤ) |>.obj T.obj₂).obj =
    stabilityMass σ
      (CategoryTheory.Triangulated.Tilting.originalHeartCoh t 0 T.obj₂).obj at hE0Mass
  change stabilityMass σ (H.shift (-1) |>.obj T.obj₃).obj =
    stabilityMass σ
      (CategoryTheory.Triangulated.Tilting.originalHeartCoh t (-1) T.obj₃).obj at hFmMass
  change stabilityMass σ (H.shift (0 : ℤ) |>.obj T.obj₃).obj =
    stabilityMass σ
      (CategoryTheory.Triangulated.Tilting.originalHeartCoh t 0 T.obj₃).obj at hF0Mass
  rw [hEmMass, hE0Mass, hFmMass, hF0Mass] at hshift
  exact hshift

/-- The semistable-left comparison on the two-cohomology window `(0, 2]`.
After rotating the semistable source to phase one, the unconditional
homological `H⁰` functor gives the six-term exact sequence

`0 ⟶ H⁻¹(E) ⟶ H⁻¹(F) ⟶ H⁰(A) ⟶ H⁰(E) ⟶ H⁰(F) ⟶ 0`.

Its image factorisations give short exact sequences with the common
phase-one kernel/image decomposition of `H⁰(A)`.  The negative-degree
sequence is controlled by the boundary-heart polygon inequality, the
degree-zero sequence by the phase-one extension comparison, and exact
same-ray additivity reassembles the source mass. -/
theorem stabilityMass_triangle_le_of_obj₁_phase_one_of_amplitude
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C)
    (h₁ : σ.slicing.P 1 T.obj₁)
    (hEgt : σ.slicing.gtProp C 0 T.obj₂)
    (hEle : σ.slicing.leProp C 2 T.obj₂)
    (hFgt : σ.slicing.gtProp C 0 T.obj₃)
    (hFle : σ.slicing.leProp C 2 T.obj₃) :
    (stabilityMass σ T.obj₂).toReal ≤
      (stabilityMass σ T.obj₁).toReal +
        (stabilityMass σ T.obj₃).toReal := by
  have hEamp := stabilityMass_toReal_eq_heartCoh_negOne_add_zero
    σ T.obj₂ hEgt hEle
  have hFamp := stabilityMass_toReal_eq_heartCoh_negOne_add_zero
    σ T.obj₃ hFgt hFle
  have hcoh := stabilityMass_heartCoh_negOne_zero_triangle_le_of_obj₁_phase_one
    σ T hT h₁
  linarith only [hEamp, hFamp, hcoh]

/-- Mass is subadditive for a distinguished triangle whose first object lies
in the phase-one slice.  The proof first cuts the middle object at phase zero;
the common lower tail splits off exactly from both the middle and right
objects.  It then cuts the remaining right object at phase two; the common
upper head again splits off exactly.  The residual triangle lies in the
two-cohomology window `(0, 2]`, where
`stabilityMass_triangle_le_of_obj₁_phase_one_of_amplitude` applies. -/
theorem stabilityMass_triangle_le_of_obj₁_phase_one
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C) (h₁ : σ.slicing.P 1 T.obj₁) :
    (stabilityMass σ T.obj₂).toReal ≤
      (stabilityMass σ T.obj₁).toReal +
        (stabilityMass σ T.obj₃).toReal := by
  have hAgt0 : σ.slicing.gtProp C 0 T.obj₁ :=
    σ.slicing.gtProp_of_semistable C h₁ (by norm_num)
  have hAle2 : σ.slicing.leProp C 2 T.obj₁ :=
    σ.slicing.leProp_of_semistable C h₁ (by norm_num)
  have hAshiftP : σ.slicing.P 2 (T.obj₁⟦(1 : ℤ)⟧) := by
    convert (σ.slicing.shift_int C 1 T.obj₁ 1).mp h₁ using 1
    all_goals norm_num
  have hAshiftgt0 : σ.slicing.gtProp C 0 (T.obj₁⟦(1 : ℤ)⟧) :=
    σ.slicing.gtProp_of_semistable C hAshiftP (by norm_num)
  have hAshiftle2 : σ.slicing.leProp C 2 (T.obj₁⟦(1 : ℤ)⟧) :=
    σ.slicing.leProp_of_semistable C hAshiftP le_rfl

  obtain ⟨FE⟩ := σ.slicing.hn_exists T.obj₂
  obtain ⟨Epos, Elow, GEpos, GElow, iE, qE, dE,
      hTE, hEposgt, hElowle, _hElowBound, _hEposContain⟩ :=
    CategoryTheory.Triangulated.HNFiltration.exists_split_at_cutoff C FE 0
  have hEposgtP : σ.slicing.gtProp C 0 Epos := by
    by_cases hn : GEpos.n = 0
    · exact Or.inl (GEpos.isZero_of_length_zero hn)
    · exact σ.slicing.gtProp_of_hn C GEpos 0 hEposgt
        (Nat.pos_of_ne_zero hn)
  have hElowleP : σ.slicing.leProp C 0 Elow := by
    by_cases hn : GElow.n = 0
    · exact Or.inl (GElow.isZero_of_length_zero hn)
    · exact σ.slicing.leProp_of_hn C GElow 0 hElowle
        (Nat.pos_of_ne_zero hn)
  have hfq : T.mor₁ ≫ qE = 0 :=
    σ.slicing.zero_of_gtProp_leProp_general C 0 hAgt0 hElowleP (T.mor₁ ≫ qE)
  obtain ⟨u, hu⟩ := Triangle.coyoneda_exact₂
    (Triangle.mk iE qE dE) hTE T.mor₁ hfq
  obtain ⟨Fpos, v, w, hU⟩ := distinguished_cocone_triangle u
  let U : Triangle C := Triangle.mk u v w
  let oct := Triangulated.someOctahedron hu.symm hU hTE hT
  have hFposgt : σ.slicing.gtProp C 0 Fpos := by
    exact σ.slicing.gtProp_of_triangle C 0 hEposgtP hAshiftgt0
      (rot_of_distTriang U hU)
  have hmassE := stabilityMass_toReal_triangle_eq_add_of_gtProp_leProp
    σ iE qE dE hTE 0 hEposgtP hElowleP
  have hmassF := stabilityMass_toReal_triangle_eq_add_of_gtProp_leProp
    σ oct.triangle.mor₁ oct.triangle.mor₂ oct.triangle.mor₃
      oct.mem 0 hFposgt hElowleP
  change (stabilityMass σ T.obj₂).toReal =
    (stabilityMass σ Epos).toReal + (stabilityMass σ Elow).toReal at hmassE
  change (stabilityMass σ T.obj₃).toReal =
    (stabilityMass σ Fpos).toReal + (stabilityMass σ Elow).toReal at hmassF

  obtain ⟨FF⟩ := σ.slicing.hn_exists Fpos
  obtain ⟨Fhigh, Flow, GFhigh, GFlow, iF, qF, dF,
      hTF, hFhighgt, hFlowle, _hFlowBound, _hFhighContain⟩ :=
    CategoryTheory.Triangulated.HNFiltration.exists_split_at_cutoff C FF 2
  have hFhighgtP : σ.slicing.gtProp C 2 Fhigh := by
    by_cases hn : GFhigh.n = 0
    · exact Or.inl (GFhigh.isZero_of_length_zero hn)
    · exact σ.slicing.gtProp_of_hn C GFhigh 2 hFhighgt
        (Nat.pos_of_ne_zero hn)
  have hFlowleP : σ.slicing.leProp C 2 Flow := by
    by_cases hn : GFlow.n = 0
    · exact Or.inl (GFlow.isZero_of_length_zero hn)
    · exact σ.slicing.leProp_of_hn C GFlow 2 hFlowle
        (Nat.pos_of_ne_zero hn)
  have hiFw : iF ≫ U.mor₃ = 0 :=
    σ.slicing.zero_of_gtProp_leProp_general C 2 hFhighgtP hAshiftle2
      (iF ≫ U.mor₃)
  obtain ⟨jF, hjF⟩ := Triangle.coyoneda_exact₃ U hU iF hiFw
  obtain ⟨Eamp, pE, dAmp, hHE⟩ := distinguished_cocone_triangle jF
  let HE : Triangle C := Triangle.mk jF pE dAmp
  let octHigh := Triangulated.someOctahedron hjF.symm hHE
    (rot_of_distTriang U hU) hTF
  let Tamp : Triangle C := Triangle.mk (U.mor₁ ≫ pE)
    octHigh.m₁ octHigh.m₃
  have hTamp : Tamp ∈ distTriang C := by
    rw [rotate_distinguished_triangle]
    change Triangle.mk octHigh.m₁ octHigh.m₃
      (-((shiftFunctor C (1 : ℤ)).map (U.mor₁ ≫ pE))) ∈ distTriang C
    rw [Functor.map_comp, ← Preadditive.neg_comp]
    simpa [octHigh, HE, U] using octHigh.mem
  have hEample2 : σ.slicing.leProp C 2 Eamp := by
    exact σ.slicing.leProp_of_triangle C 2 hAle2 hFlowleP hTamp
  have hFhighgt0 : σ.slicing.gtProp C 0 Fhigh :=
    σ.slicing.gtProp_anti C (by norm_num : (0 : ℝ) ≤ 2) Fhigh hFhighgtP
  have hFhighShiftP : σ.slicing.gtProp C 0 (Fhigh⟦(1 : ℤ)⟧) := by
    have h := σ.slicing.gtProp_shift C 2 Fhigh 1 hFhighgtP
    exact σ.slicing.gtProp_anti C (by norm_num : (0 : ℝ) ≤ 3)
      (Fhigh⟦(1 : ℤ)⟧) (by
        convert h using 1
        all_goals norm_num)
  have hEampgt0 : σ.slicing.gtProp C 0 Eamp := by
    exact σ.slicing.gtProp_of_triangle C 0 hEposgtP hFhighShiftP
      (rot_of_distTriang HE hHE)
  have hFlowgt0 : σ.slicing.gtProp C 0 Flow := by
    exact σ.slicing.gtProp_of_triangle C 0 hEampgt0 hAshiftgt0
      (rot_of_distTriang Tamp hTamp)
  have hmassEpos := stabilityMass_toReal_triangle_eq_add_of_gtProp_leProp
    σ jF pE dAmp hHE 2 hFhighgtP hEample2
  have hmassFpos := stabilityMass_toReal_triangle_eq_add_of_gtProp_leProp
    σ iF qF dF hTF 2 hFhighgtP hFlowleP
  have hamp := stabilityMass_triangle_le_of_obj₁_phase_one_of_amplitude
    σ Tamp hTamp h₁ hEampgt0 hEample2 hFlowgt0 hFlowleP
  change (stabilityMass σ Epos).toReal =
    (stabilityMass σ Fhigh).toReal + (stabilityMass σ Eamp).toReal at hmassEpos
  change (stabilityMass σ Fpos).toReal =
    (stabilityMass σ Fhigh).toReal + (stabilityMass σ Flow).toReal at hmassFpos
  change (stabilityMass σ Eamp).toReal ≤
    (stabilityMass σ T.obj₁).toReal + (stabilityMass σ Flow).toReal at hamp
  linarith

/-- The second mass-triangle milestone: the triangle inequality whenever the
left endpoint is semistable, at an arbitrary phase.  A lifted rotation moves
that phase to one and preserves every object's HN mass. -/
theorem stabilityMassSemistableLeftTriangleInequality :
    StabilityMassSemistableLeftTriangleInequality (C := C) (v := v) := by
  intro σ T hT φ h₁
  let θ : ℝ := 1 - φ
  have hrot : (liftedRotation θ • σ).slicing.P 1 T.obj₁ := by
    change σ.slicing.P (1 - θ) T.obj₁
    convert h₁ using 1
    all_goals simp [θ]
  have h := stabilityMass_triangle_le_of_obj₁_phase_one
    (liftedRotation θ • σ) T hT hrot
  simpa using h

/-- Harder--Narasimhan mass is subadditive along every distinguished triangle. -/
theorem stabilityMassTriangleInequality :
    StabilityMassTriangleInequality (C := C) (v := v) :=
  stabilityMassTriangleInequality_of_semistable_obj₁
    stabilityMassSemistableLeftTriangleInequality

/-- Full-distance balls form a neighbourhood basis for the pre-existing
Section 6 topology.  This closes the explicit mass-triangle premise of the
topology comparison without installing a second topology or metric instance. -/
@[cites "stmt:a520a8d4f877:bridgeland2007.prop-8.1" (relation := no_claim)
        (note := "Unconditional topology comparison obtained by applying the existing conditional comparison to the proved HN mass-triangle theorem. The citation remains no_claim pending exact-head source-faithfulness review and owner acceptance; no topology or metric instance is installed.")]
theorem stabilityDistanceTopologyCompatible :
    StabilityDistanceTopologyCompatible (C := C) (v := v) :=
  stabilityDistanceTopologyCompatible_of_mass_triangle
    stabilityMassTriangleInequality

set_option maxHeartbeats 200000

/-- The global distinguished-triangle inequality restricts to the heart-level
short-exact inequality. -/
theorem stabilityMassHeartShortExactInequality_of_triangle
    (htriangle : StabilityMassTriangleInequality (C := C) (v := v)) :
    StabilityMassHeartShortExactInequality (C := C) (v := v) := by
  intro σ S hS
  obtain ⟨δ, hT⟩ := heartShortExact_exists_distinguished_triangle σ S hS
  exact htriangle σ (Triangle.mk S.f.hom S.g.hom δ) hT

/-- A short exact sequence in the heart of the slicing satisfies the mass
inequality when its middle object is semistable in the ambient slicing. -/
theorem stabilityMass_heart_shortExact_le_of_obj₂_semistable
    (σ : StabilityCondition.WithClassMap C v)
    (S : ShortComplex σ.slicing.toTStructure.heart.FullSubcategory)
    (hS : S.ShortExact) {φ : ℝ} (h₂ : σ.slicing.P φ S.X₂.obj) :
    (stabilityMass σ S.X₂.obj).toReal ≤
      (stabilityMass σ S.X₁.obj).toReal +
        (stabilityMass σ S.X₃.obj).toReal := by
  obtain ⟨δ, hT⟩ := heartShortExact_exists_distinguished_triangle σ S hS
  exact stabilityMass_triangle_le_of_obj₂_semistable σ
    (Triangle.mk S.f.hom S.g.hom δ) hT h₂

/-- A short exact sequence in the heart satisfies the mass inequality when
its endpoint objects are semistable of the same phase. -/
theorem stabilityMass_heart_shortExact_le_of_same_phase
    (σ : StabilityCondition.WithClassMap C v)
    (S : ShortComplex σ.slicing.toTStructure.heart.FullSubcategory)
    (hS : S.ShortExact) (φ : ℝ)
    (h₁ : σ.slicing.P φ S.X₁.obj) (h₃ : σ.slicing.P φ S.X₃.obj) :
    (stabilityMass σ S.X₂.obj).toReal ≤
      (stabilityMass σ S.X₁.obj).toReal +
        (stabilityMass σ S.X₃.obj).toReal := by
  obtain ⟨δ, hT⟩ := heartShortExact_exists_distinguished_triangle σ S hS
  exact stabilityMass_triangle_le_of_same_phase σ
    (Triangle.mk S.f.hom S.g.hom δ) hT φ h₁ h₃

end

end CategoryTheory.Triangulated
