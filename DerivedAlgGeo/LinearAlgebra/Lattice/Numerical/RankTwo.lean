/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.Lattice.Arithmetic.TorsionFree
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# A rank-two numerical lattice model

A deliberately *concrete* stand-in for `K_num(Ku(X)) ≅ ℤ²`.

**This is not the Kuznetsov component's numerical Grothendieck group.** It is
the rank-2 torsion-free lattice that group is isomorphic to, and every lemma
here is a statement about that lattice alone. The identification itself is
geometry, lives upstream of anything Mathlib can express today, and is tracked
as an assumption-frontier obligation — never discharged here.

Keeping the two apart is the whole point: a proof over `Fin 2 → ℤ` is a
theorem about any rank-2 torsion-free lattice, not yet a theorem about a
surface.
-/

namespace IntegralLattice

/-- The rank-2 numerical lattice model. -/
abbrev NumLattice : Type := Fin 2 → ℤ

example : NoZeroSMulDivisors ℤ NumLattice := inferInstance

theorem finrank_numLattice : Module.finrank ℤ NumLattice = 2 := by
  simp

/-- Rank-component non-vanishing: a lattice vector with any nonzero component
is nonzero. The §8 "rank component does not vanish" step. -/
theorem ne_zero_of_apply_ne_zero {v : NumLattice} {i : Fin 2} (h : v i ≠ 0) :
    v ≠ 0 := by
  intro hv
  exact h (by rw [hv]; rfl)

/-- The doubling step, specialised to the rank-2 model. -/
theorem eq_zero_of_two_zsmul_eq_zero_num {v : NumLattice} (h : (2 : ℤ) • v = 0) :
    v = 0 :=
  eq_zero_of_two_zsmul_eq_zero h

end IntegralLattice
