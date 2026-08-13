/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.Deformation.PhaseArithmetic
import BridgelandStabLean.Foundation.StabilityCondition

/-!
# Skewed stability data on an owner interval

A perturbed charge need not itself define a stability condition yet.  On a
thin interval it supplies a skewed phase whenever it is nonzero on the old
semistable factors.  This module owns that intermediate object and its
triangle-additive phase comparisons.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

namespace BridgelandStabLean.Foundation.Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ)

/-- A perturbed central charge on the owner interval `P((a,b))`, with a branch
centre and nonvanishing on the original semistable factors in that interval. -/
structure SkewedStabilityFunction (s : Slicing C) (a b : ℝ) where
  /-- The perturbed central charge. -/
  W : Λ →+ ℂ
  /-- The centre of the chosen phase branch. -/
  α : ℝ
  /-- The branch centre lies in the interval. -/
  centre_mem : a < α ∧ α < b
  /-- The perturbed charge does not vanish on old nonzero semistable factors. -/
  nonzero : ∀ (E : C) (φ : ℝ), a < φ → φ < b →
    s.P φ E → ¬IsZero E → W (classOf C v E) ≠ 0

namespace SkewedStabilityFunction

variable {C v} {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}
variable {s : Slicing C} {a b : ℝ}

/-- The perturbed charge of an ambient object. -/
abbrev charge (F : SkewedStabilityFunction C κ s a b) (E : C) : ℂ :=
  F.W (classOf C κ E)

/-- The perturbed phase on the branch selected by the skewed data. -/
abbrev phase (F : SkewedStabilityFunction C κ s a b) (E : C) : ℝ :=
  relativePhase (F.charge E) F.α

/-- Nonvanishing of an object's perturbed charge. -/
abbrev ChargeNe (F : SkewedStabilityFunction C κ s a b) (E : C) : Prop :=
  F.charge E ≠ 0

/-- Equal perturbed charges have equal phases. -/
theorem phase_congr (F : SkewedStabilityFunction C κ s a b) {E E' : C}
    (h : F.charge E = F.charge E') : F.phase E = F.phase E' := by
  simp only [phase, h]

/-- Isomorphic objects have equal perturbed phases. -/
theorem phase_iso (F : SkewedStabilityFunction C κ s a b) {E E' : C}
    (e : E ≅ E') : F.phase E = F.phase E' :=
  F.phase_congr (congrArg F.W (classOf_iso C κ e))

/-- Perturbed charges are additive along distinguished triangles. -/
theorem charge_triangle (F : SkewedStabilityFunction C κ s a b)
    (T : Triangle C) (hT : T ∈ distTriang C) :
    F.charge T.obj₂ = F.charge T.obj₁ + F.charge T.obj₃ := by
  simp only [charge, classOf_triangle C κ T hT, map_add]

/-- The charge-level phase see-saw for ambient objects. -/
theorem phase_seesaw (F : SkewedStabilityFunction C κ s a b)
    {E E₁ E₂ : C} {ψ : ℝ}
    (hsum : F.charge E₁ + F.charge E₂ = F.charge E)
    (hψ : F.phase E = ψ)
    (hE₁_range : F.phase E₁ ∈ Set.Ioc (ψ - 1) ψ)
    (hE₂_ne : F.ChargeNe E₂)
    (hE₂_range : F.phase E₂ ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    ψ ≤ F.phase E₂ :=
  relativePhase_seesaw hsum hψ hE₁_range hE₂_ne hE₂_range

/-- Strict charge-level phase see-saw for ambient objects. -/
theorem phase_seesaw_strict (F : SkewedStabilityFunction C κ s a b)
    {E E₁ E₂ : C} {ψ : ℝ}
    (hsum : F.charge E₁ + F.charge E₂ = F.charge E)
    (hψ : F.phase E = ψ)
    (hE₂_lt : F.phase E₂ < ψ)
    (hE₂_ne : F.ChargeNe E₂)
    (hE₂_range : F.phase E₂ ∈ Set.Ioo (ψ - 1) (ψ + 1))
    (hE₁_range : F.phase E₁ ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    ψ < F.phase E₁ :=
  relativePhase_seesaw_strict hsum hψ hE₂_lt hE₂_ne
    hE₂_range hE₁_range

/-- An interval object is semistable for the perturbed charge when every
admissible nonzero subobject triangle has phase at most its phase. -/
structure IsSemistable (F : SkewedStabilityFunction C κ s a b)
    (E : C) (ψ : ℝ) : Prop where
  /-- The object lies in the old thin interval. -/
  interval : s.intervalProp C a b E
  /-- The object is nonzero. -/
  nonzero : ¬IsZero E
  /-- Its perturbed charge is nonzero. -/
  charge_ne : F.ChargeNe E
  /-- Its chosen perturbed phase is `ψ`. -/
  phase_eq : F.phase E = ψ
  /-- Every nonzero subobject represented by an interval triangle has phase at
  most `ψ`. -/
  phase_le_of_triangle : ∀ ⦃K Q : C⦄ ⦃i : K ⟶ E⦄ ⦃q : E ⟶ Q⦄
    ⦃δ : Q ⟶ K⟦(1 : ℤ)⟧⦄,
    Triangle.mk i q δ ∈ distTriang C →
    s.intervalProp C a b K → s.intervalProp C a b Q →
    ¬IsZero K → F.phase K ≤ ψ

/-- A perturbed-semistable object's phase lies on its chosen branch. -/
theorem IsSemistable.phase_mem_Ioc {F : SkewedStabilityFunction C κ s a b}
    {E : C} {ψ : ℝ} (h : F.IsSemistable E ψ) :
    ψ ∈ Set.Ioc (F.α - 1) (F.α + 1) := by
  rw [← h.phase_eq]
  exact relativePhase_mem_Ioc _ _

/-- Polar form of the charge of a perturbed-semistable object. -/
theorem IsSemistable.charge_polar {F : SkewedStabilityFunction C κ s a b}
    {E : C} {ψ : ℝ} (h : F.IsSemistable E ψ) :
    F.charge E = (‖F.charge E‖ : ℂ) *
      Complex.exp (↑(Real.pi * ψ) * Complex.I) := by
  rw [← h.phase_eq]
  exact relativePhase_polar _ _

end SkewedStabilityFunction

end BridgelandStabLean.Foundation.Deformation
