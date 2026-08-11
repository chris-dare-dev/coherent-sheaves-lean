/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.Numerical.GrothendieckGroup.EulerPairing
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Int.Basic

/-!
# The numerical Grothendieck lattice

The numerical Grothendieck group is the quotient by the radical of the Euler pairing.  This
file makes that construction explicit from `NumericalVariety.chi₂` and records the precise
finiteness input needed before the quotient is a lattice.

The Euler pairing supplied by `NumericalVariety` is `ℚ`-valued.  Consequently the descended
pairing below is also `ℚ`-valued; no integrality statement is silently assumed.  The integral
object is its underlying finite free `ℤ`-module.

## Main results

* `NumericalVariety.leftRadical` and `NumericalVariety.rightRadical` are the two Euler radicals.
* `NumericalVariety.leftRadical_eq_rightRadical` identifies them when the Euler form is symmetric.
* `NumericalVariety.NumericalQuotient` is the quotient by the radical.
* `NumericalVariety.numericalPairing` is the descended, nondegenerate pairing.
* `ZLattice` packages a finite free abelian group; `numericalZLattice` constructs one from
  explicit finite-generation and quotient torsion-freeness hypotheses.
* `K3.numericalPairing_mk_eq_neg_mukaiPairing` fixes the K3 sign convention.
-/

universe u v w

namespace AlgebraicGeometry.Numerical

/-- A `ℤ`-lattice is a finite free abelian group.

This is deliberately distinct from Mathlib's `IsZLattice`, which concerns discrete subgroups
of normed real or complex vector spaces.  This algebraic notion is the one consumed by
Bridgeland-stability constructions. -/
class ZLattice (Λ : Type w) [AddCommGroup Λ] : Prop where
  /-- The lattice is finitely generated over `ℤ`. -/
  toModuleFinite : Module.Finite ℤ Λ
  /-- The lattice is free over `ℤ`. -/
  toModuleFree : Module.Free ℤ Λ

attribute [instance] ZLattice.toModuleFinite ZLattice.toModuleFree

namespace ZLattice

/-- A finitely generated torsion-free abelian group is a `ℤ`-lattice.

Both hypotheses are explicit.  Freeness is the structure theorem for finite modules over the
principal ideal domain `ℤ`. -/
theorem ofFiniteTorsionFree (Λ : Type w) [AddCommGroup Λ]
    [Module.Finite ℤ Λ] [Module.IsTorsionFree ℤ Λ] : ZLattice Λ := by
  exact
    { toModuleFinite := inferInstance
      toModuleFree := Module.free_of_finite_type_torsion_free' }

end ZLattice

namespace NumericalVariety

variable {n : ℕ} {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety n A N]

/-- The Euler pairing with its second argument packaged as an additive homomorphism. -/
noncomputable def eulerPairingRow (E : N) : N →+ ℚ :=
  AddMonoidHom.mk' (chi₂ (A := A) E) (chi₂_add_right E)

/-- The Euler pairing as a biadditive homomorphism `N →+ (N →+ ℚ)`. -/
noncomputable def eulerPairing : N →+ (N →+ ℚ) :=
  AddMonoidHom.mk' (eulerPairingRow (A := A)) fun E F => by
    ext G
    exact chi₂_add_left E F G

/-- The transposed Euler pairing as a biadditive homomorphism. -/
noncomputable def eulerPairingFlip : N →+ (N →+ ℚ) :=
  AddMonoidHom.mk' (fun F => AddMonoidHom.mk' (fun E => chi₂ (A := A) E F)
    (fun E G => chi₂_add_left E G F)) fun E F => by
      ext G
      exact chi₂_add_right G E F

@[simp]
theorem eulerPairing_apply (E F : N) : eulerPairing (A := A) E F = chi₂ (A := A) E F :=
  rfl

@[simp]
theorem eulerPairingFlip_apply (E F : N) :
    eulerPairingFlip (A := A) E F = chi₂ (A := A) F E :=
  rfl

/-- The left radical: classes pairing to zero against every class on the right. -/
noncomputable def leftRadical : Submodule ℤ N :=
  AddSubgroup.toIntSubmodule (eulerPairing (A := A)).ker

/-- The right radical: classes pairing to zero against every class on the left. -/
noncomputable def rightRadical : Submodule ℤ N :=
  AddSubgroup.toIntSubmodule (eulerPairingFlip (A := A)).ker

theorem mem_leftRadical_iff (E : N) :
    E ∈ leftRadical (A := A) ↔ ∀ F : N, chi₂ (A := A) E F = 0 := by
  rw [leftRadical]
  change E ∈ (eulerPairing (A := A)).ker ↔ _
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro h F
    simpa using DFunLike.congr_fun h F
  · intro h
    ext F
    simpa using h F

theorem mem_rightRadical_iff (F : N) :
    F ∈ rightRadical (A := A) ↔ ∀ E : N, chi₂ (A := A) E F = 0 := by
  rw [rightRadical]
  change F ∈ (eulerPairingFlip (A := A)).ker ↔ _
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro h E
    simpa using DFunLike.congr_fun h E
  · intro h
    ext E
    simpa using h E

/-- The symmetry hypothesis under which the project uses a single Euler radical. -/
def IsEulerPairingSymmetric : Prop :=
  ∀ E F : N, chi₂ (A := A) E F = chi₂ (A := A) F E

/-- For a symmetric Euler form, its left and right radicals agree. -/
theorem leftRadical_eq_rightRadical (hSymm : IsEulerPairingSymmetric (A := A) (N := N)) :
    leftRadical (A := A) (N := N) = rightRadical (A := A) (N := N) := by
  ext E
  rw [mem_leftRadical_iff, mem_rightRadical_iff]
  constructor
  · intro h F
    rw [hSymm F E]
    exact h F
  · intro h F
    rw [hSymm E F]
    exact h F

/-- The numerical Grothendieck quotient by the left Euler radical.

Under `IsEulerPairingSymmetric`, `leftRadical_eq_rightRadical` shows that this is equivalently
the quotient by the right radical. -/
abbrev NumericalQuotient (n : ℕ) (A : Type u) (N : Type v) [CommRing A] [Algebra ℚ A]
    [AddCommGroup N] [NumericalVariety n A N] :=
  N ⧸ leftRadical (n := n) (A := A) (N := N)

/-- Descend the right argument of the Euler pairing to the numerical quotient. -/
noncomputable def eulerPairingDescendRight
    (hSymm : IsEulerPairingSymmetric (A := A) (N := N)) (E : N) :
    NumericalQuotient n A N →+ ℚ :=
  QuotientAddGroup.lift (leftRadical (n := n) (A := A) (N := N)).toAddSubgroup
    (eulerPairingRow (A := A) E) <| by
    intro F hF
    rw [AddMonoidHom.mem_ker]
    change chi₂ (A := A) E F = 0
    rw [hSymm E F]
    exact (mem_leftRadical_iff (A := A) F).mp hF E

@[simp]
theorem eulerPairingDescendRight_mk
    (hSymm : IsEulerPairingSymmetric (A := A) (N := N)) (E F : N) :
    eulerPairingDescendRight (A := A) hSymm E (Submodule.Quotient.mk F) =
      chi₂ (A := A) E F :=
  rfl

/-- The Euler pairing with its right argument descended, still additive in the left argument. -/
noncomputable def eulerPairingToQuotient
    (hSymm : IsEulerPairingSymmetric (A := A) (N := N)) :
    N →+ (NumericalQuotient n A N →+ ℚ) :=
  AddMonoidHom.mk' (eulerPairingDescendRight (A := A) hSymm) fun E F => by
    ext q
    refine Submodule.Quotient.induction_on _ q ?_
    intro G
    exact chi₂_add_left E F G

@[simp]
theorem eulerPairingToQuotient_mk
    (hSymm : IsEulerPairingSymmetric (A := A) (N := N)) (E F : N) :
    eulerPairingToQuotient (A := A) hSymm E (Submodule.Quotient.mk F) =
      chi₂ (A := A) E F :=
  rfl

/-- The Euler pairing descended to the numerical quotient in both arguments. -/
noncomputable def numericalPairing
    (hSymm : IsEulerPairingSymmetric (A := A) (N := N)) :
    NumericalQuotient n A N →+ (NumericalQuotient n A N →+ ℚ) :=
  QuotientAddGroup.lift (leftRadical (n := n) (A := A) (N := N)).toAddSubgroup
    (eulerPairingToQuotient (A := A) hSymm) <| by
      intro E hE
      rw [AddMonoidHom.mem_ker]
      ext q
      refine Submodule.Quotient.induction_on _ q ?_
      intro F
      exact (mem_leftRadical_iff (A := A) E).mp hE F

@[simp]
theorem numericalPairing_mk
    (hSymm : IsEulerPairingSymmetric (A := A) (N := N)) (E F : N) :
    numericalPairing (A := A) hSymm (Submodule.Quotient.mk E) (Submodule.Quotient.mk F) =
      chi₂ (A := A) E F :=
  rfl

/-- The descended pairing remains symmetric. -/
theorem numericalPairing_symm
    (hSymm : IsEulerPairingSymmetric (A := A) (N := N))
    (x y : NumericalQuotient n A N) :
    numericalPairing (A := A) hSymm x y = numericalPairing (A := A) hSymm y x := by
  refine Submodule.Quotient.induction_on _ x fun E => ?_
  refine Submodule.Quotient.induction_on _ y fun F => ?_
  exact hSymm E F

/-- The descended pairing has zero left radical, by construction. -/
theorem numericalPairing_left_nondegenerate
    (hSymm : IsEulerPairingSymmetric (A := A) (N := N))
    (x : NumericalQuotient n A N)
    (hx : ∀ y : NumericalQuotient n A N, numericalPairing (A := A) hSymm x y = 0) :
    x = 0 := by
  revert hx
  refine Submodule.Quotient.induction_on _ x fun E hx => ?_
  rw [Submodule.Quotient.mk_eq_zero, mem_leftRadical_iff]
  intro F
  simpa using hx (Submodule.Quotient.mk F)

/-- The descended pairing has zero right radical as well. -/
theorem numericalPairing_right_nondegenerate
    (hSymm : IsEulerPairingSymmetric (A := A) (N := N))
    (y : NumericalQuotient n A N)
    (hy : ∀ x : NumericalQuotient n A N, numericalPairing (A := A) hSymm x y = 0) :
    y = 0 := by
  apply numericalPairing_left_nondegenerate (A := A) hSymm y
  intro x
  rw [numericalPairing_symm (A := A) hSymm]
  exact hy x

/-- The kernel of the descended pairing is zero. -/
theorem numericalPairing_ker_eq_bot
    (hSymm : IsEulerPairingSymmetric (A := A) (N := N)) :
    (numericalPairing (A := A) hSymm).ker = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [AddSubgroup.mem_bot]
    apply numericalPairing_left_nondegenerate (A := A) hSymm x
    intro y
    have hzero := AddMonoidHom.mem_ker.mp hx
    simpa using DFunLike.congr_fun hzero y
  · exact bot_le

/-- The numerical quotient is a `ℤ`-lattice once the original group is finitely generated and
the quotient is torsion-free.

Finite generation passes automatically to the quotient.  Torsion-freeness does not pass to an
arbitrary quotient, so it is intentionally required on `NumericalQuotient` itself. -/
theorem numericalZLattice [Module.Finite ℤ N]
    [Module.IsTorsionFree ℤ (NumericalQuotient n A N)] :
    ZLattice (NumericalQuotient n A N) := by
  letI : Module.Finite ℤ (NumericalQuotient n A N) :=
    Module.Finite.quotient ℤ (leftRadical (n := n) (A := A) (N := N))
  exact ZLattice.ofFiniteTorsionFree _

end NumericalVariety

namespace K3

open NumericalVariety

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety 2 A N] [IsK3 A N]

/-- A K3 Euler pairing satisfies the symmetry hypothesis used by the numerical quotient. -/
theorem isEulerPairingSymmetric : IsEulerPairingSymmetric (A := A) (N := N) :=
  fun E F => chi₂_comm E F

/-- On a K3, the two Euler radicals agree. -/
theorem leftRadical_eq_rightRadical :
    NumericalVariety.leftRadical (A := A) (N := N) =
      NumericalVariety.rightRadical (A := A) (N := N) :=
  NumericalVariety.leftRadical_eq_rightRadical (A := A) (N := N)
    isEulerPairingSymmetric

/-- On representatives, the numerical quotient pairing is minus the Mukai pairing.

Thus quotienting and descending preserve exactly the sign convention fixed by
`chi₂_eq_neg_mukaiPairing`. -/
theorem numericalPairing_mk_eq_neg_mukaiPairing (E F : N) :
    NumericalVariety.numericalPairing (A := A) (N := N) isEulerPairingSymmetric
        (Submodule.Quotient.mk E) (Submodule.Quotient.mk F) =
      -mukaiPairing (A := A) E F := by
  rw [NumericalVariety.numericalPairing_mk, chi₂_eq_neg_mukaiPairing]

end K3

end AlgebraicGeometry.Numerical
