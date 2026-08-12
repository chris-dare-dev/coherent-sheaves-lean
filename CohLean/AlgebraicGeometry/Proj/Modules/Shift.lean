/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import CohLean.AlgebraicGeometry.Proj.Modules.AssociatedSheaf

/-!
# Shifts of naturally graded modules

`Proj` starts from an `ℕ`-graded ring, while twisting sheaves are conventionally indexed by
`ℤ`.  This file keeps that boundary visible.

* `natShift 𝓜 d` has degree-`n` piece `𝓜 (n + d)` and composes strictly.
* `intShift 𝓜 d` uses the same formula with `n + d : ℤ`, extending `𝓜` by the zero subgroup
  in negative degrees.  It is a one-step shift of the original natural grading.  Iterated mixed
  integer shifts are deliberately not identified at the graded-module level: truncation at degree
  zero makes that false before passing to associated sheaves.

Our sign convention is therefore `M(d)ₙ = Mₙ₊d`.
-/

noncomputable section

open scoped Pointwise

namespace CohLean.AlgebraicGeometry.Proj

universe u

variable {A M σA σM : Type u}
variable [CommRing A] [AddCommGroup M] [Module A M]
variable [SetLike σA A] [AddSubgroupClass σA A]
variable [SetLike σM M] [AddSubgroupClass σM M]
variable (𝒜 : ℕ → σA) (𝓜 : ℕ → σM)
variable [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜]

/-! ## Natural shifts -/

/-- The natural shift with convention `M(d)ₙ = Mₙ₊d`. -/
def natShift (d : ℕ) : ℕ → σM := fun n => 𝓜 (n + d)

instance natShiftGradedSMul (d : ℕ) : SetLike.GradedSMul 𝒜 (natShift 𝓜 d) where
  smul_mem {i j} {a m} ha hm := by
    change m ∈ 𝓜 (j + d) at hm
    have h := SetLike.GradedSMul.smul_mem (A := 𝒜) (B := 𝓜) ha hm
    change a • m ∈ 𝓜 (i + (j + d)) at h
    change a • m ∈ 𝓜 ((i + j) + d)
    simpa only [Nat.add_assoc] using h

@[simp]
theorem natShift_apply (d n : ℕ) : natShift 𝓜 d n = 𝓜 (n + d) := rfl

@[simp]
theorem natShift_zero : natShift 𝓜 0 = 𝓜 := by
  funext n
  simp [natShift]

@[simp]
theorem natShift_add (d e : ℕ) :
    natShift (natShift 𝓜 d) e = natShift 𝓜 (d + e) := by
  funext n
  simp [natShift, Nat.add_assoc, Nat.add_comm d e]

/-! ## Integer shifts by zero extension -/

/-- The degree-`n` subgroup of the integer shift.  A nonzero element belongs precisely when it
lies in a natural graded piece whose integer degree equals `n + d`; zero is retained when that
integer is negative. -/
def intShiftPiece (d : ℤ) (n : ℕ) : AddSubgroup M where
  carrier := {m | m = 0 ∨ ∃ k : ℕ, (k : ℤ) = (n : ℤ) + d ∧ m ∈ 𝓜 k}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro x y (rfl | ⟨k, hk, hx⟩) (rfl | ⟨l, hl, hy⟩)
    · exact Or.inl (zero_add 0)
    · exact Or.inr ⟨l, hl, by simpa using hy⟩
    · exact Or.inr ⟨k, hk, by simpa using hx⟩
    · have hkl : k = l := Int.ofNat_inj.mp (hk.trans hl.symm)
      subst l
      exact Or.inr ⟨k, hk, add_mem hx hy⟩
  neg_mem' := by
    rintro x (rfl | ⟨k, hk, hx⟩)
    · exact Or.inl (neg_zero)
    · exact Or.inr ⟨k, hk, neg_mem hx⟩

/-- The integer shift of a naturally graded module, using zero in negative degrees. -/
def intShift (d : ℤ) : ℕ → AddSubgroup M := fun n => intShiftPiece 𝓜 d n

@[simp]
theorem mem_intShiftPiece {d : ℤ} {n : ℕ} {m : M} :
    m ∈ intShiftPiece 𝓜 d n ↔
      m = 0 ∨ ∃ k : ℕ, (k : ℤ) = (n : ℤ) + d ∧ m ∈ 𝓜 k :=
  Iff.rfl

instance intShiftGradedSMul (d : ℤ) : SetLike.GradedSMul 𝒜 (intShift 𝓜 d) where
  smul_mem {i j} {a m} ha hm := by
    rcases hm with rfl | ⟨k, hk, hm⟩
    · exact Or.inl (smul_zero a)
    · refine Or.inr ⟨i + k, ?_,
        SetLike.GradedSMul.smul_mem (A := 𝒜) (B := 𝓜) ha hm⟩
      change ((i + k : ℕ) : ℤ) = ((i + j : ℕ) : ℤ) + d
      push_cast
      omega

@[simp]
theorem intShift_apply (d : ℤ) (n : ℕ) : intShift 𝓜 d n = intShiftPiece 𝓜 d n := rfl

/-- At shift zero the integer-shifted pieces are the original pieces, expressed as an equality
of their carriers. -/
theorem mem_intShift_zero_iff (n : ℕ) (m : M) :
    m ∈ intShift 𝓜 0 n ↔ m ∈ 𝓜 n := by
  constructor
  · rintro (rfl | ⟨k, hk, hm⟩)
    · exact zero_mem _
    · have hkn : k = n := Int.ofNat_inj.mp (by simpa using hk)
      simpa [hkn] using hm
  · intro hm
    exact Or.inr ⟨n, by simp, hm⟩

/-- A nonnegative integer shift agrees with the corresponding natural shift, at the level of
membership in each graded piece. -/
theorem mem_intShift_ofNat_iff (d n : ℕ) (m : M) :
    m ∈ intShift 𝓜 (d : ℤ) n ↔ m ∈ natShift 𝓜 d n := by
  constructor
  · rintro (rfl | ⟨k, hk, hm⟩)
    · exact zero_mem _
    · have hkn : k = n + d := Int.ofNat_inj.mp (by simpa using hk)
      simpa [natShift, hkn] using hm
  · intro hm
    exact Or.inr ⟨n + d, by simp, hm⟩

omit [AddCommGroup M] [AddSubgroupClass σM M] in
/-- Strict composition for nonnegative shifts, phrased as membership so it applies uniformly
even when the subobject types differ. -/
theorem mem_natShift_add_iff (d e n : ℕ) (m : M) :
    m ∈ natShift (natShift 𝓜 d) e n ↔ m ∈ natShift 𝓜 (d + e) n := by
  simp only [natShift_apply]
  rw [Nat.add_assoc, Nat.add_comm e d]

end CohLean.AlgebraicGeometry.Proj
