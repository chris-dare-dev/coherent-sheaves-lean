/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.Basic
import Mathlib.LinearAlgebra.BilinearForm.Isometry

/-!
# Reflection in a spherical class

For a vector `s` of a Mukai extension with `⟪s, s⟫ = -2`, the map

```
ρ_s(v) = v + ⟪v, s⟫ • s
```

is the reflection in the hyperplane `s^⊥`. The `-2` is what makes the usual
formula `v - 2⟪v,s⟫/⟪s,s⟫ · s` integral: the denominator cancels the `2`, so no
division is needed and the reflection is defined on the lattice rather than on
its rationalisation. This is the only place `IsSpherical` is used below, and it
is used exactly once, in `reflect_reflect`.

**This is not the spherical twist.** On a K3 surface, the twist `T_E` of
Seidel–Thomas acts on the Mukai lattice as `ρ_{v(E)}`, and that statement is the
eventual reason this file exists. But `T_E` is an autoequivalence of
`Dᵇ(Coh X)`, its construction needs an evaluation triangle and a functorial
cone, and none of that is available here or asserted here. `reflect` is a map
of a lattice built from a bilinear form, and every theorem below is a theorem
about **an arbitrary symmetric bilinear `ℤ`-lattice**, true whether or not any
surface exists — the same discipline `Mukai/Basic.lean` states in its own
docstring.

Note which hypotheses do what, because the split is not the expected one:

* **additivity** of `ρ_s` needs neither symmetry of `b` nor `⟪s,s⟫ = -2`. It is
  bilinearity of the pairing alone, so `reflectHom` is a `ℤ`-linear map for
  *every* `s`;
* **involutivity** needs `⟪s,s⟫ = -2` and nothing else;
* **isometry** needs symmetry of `b` as well, and fails without it — the two
  cross terms `⟪v,s⟫⟪s,w⟫` and `⟪w,s⟫⟪v,s⟫` only cancel against
  `⟪v,s⟫⟪w,s⟫⟪s,s⟫` once they are equal.

## Main results

* `reflectHom` — `ρ_s` as a `ℤ`-linear endomorphism, for arbitrary `s`.
* `reflect_reflect` — `ρ_s` is an involution when `s` is spherical.
* `pairing_reflect_reflect` — `ρ_s` preserves the pairing (symmetric `b`).
* `reflectEquiv` — the resulting `ℤ`-linear automorphism.
* `reflectIsometry` — the same map as an isometry of `pairingBilin`.
* `reflect_self` — `ρ_s s = -s`, and `reflect_of_pairing_eq_zero` — `ρ_s`
  fixes `s^⊥` pointwise. Together these say `ρ_s` is a *reflection* rather
  than merely an involutive isometry.
* `IsSpherical.reflect`, `IsIsotropic.reflect`, `expectedDim_reflect` — the
  distinguished classes of `Mukai/Basic.lean` are preserved.
-/

namespace Mukai

variable {N : Type*} [AddCommGroup N] (b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ)

/-! ### The map, and its linearity

Stated for an arbitrary `s`. Sphericity enters only from `reflect_reflect`
onwards, so everything in this section holds for every `s` and is not a
statement about spherical classes at all. -/

/-- Reflection in `s`: `ρ_s(v) = v + ⟪v, s⟫ • s`.

For spherical `s` this is the lattice reflection in `s^⊥`; for other `s` it is
still a well-defined additive map, but is neither an involution nor an
isometry. The definition deliberately takes no sphericity hypothesis so that
`reflectHom` below is available unconditionally. -/
def reflect (s v : MukaiLattice N) : MukaiLattice N :=
  v + pairing b v s • s

/-- Not `@[simp]`: unfolding `reflect` everywhere would put `reflect_zero`,
`reflect_self` and `reflect_neg_left` out of simp-normal form. Rewrite with it
explicitly. -/
theorem reflect_apply (s v : MukaiLattice N) :
    reflect b s v = v + pairing b v s • s :=
  rfl

@[simp]
theorem reflect_zero (s : MukaiLattice N) : reflect b s 0 = 0 := by
  simp [reflect]

theorem reflect_add (s v w : MukaiLattice N) :
    reflect b s (v + w) = reflect b s v + reflect b s w := by
  simp only [reflect, pairing_add_left, add_smul]
  abel

theorem reflect_smul (a : ℤ) (s v : MukaiLattice N) :
    reflect b s (a • v) = a • reflect b s v := by
  simp only [reflect, pairing_smul_left, smul_add, mul_smul]

theorem reflect_neg (s v : MukaiLattice N) :
    reflect b s (-v) = -reflect b s v := by
  simp only [reflect, pairing_neg_left, neg_smul, neg_add_rev]
  abel

/-- `ρ_s` as a `ℤ`-linear endomorphism of the Mukai extension.

No hypothesis on `s`: additivity is bilinearity of `pairing`, nothing more. -/
def reflectHom (s : MukaiLattice N) : MukaiLattice N →ₗ[ℤ] MukaiLattice N where
  toFun := reflect b s
  map_add' := reflect_add b s
  map_smul' := by intro a v; simpa using reflect_smul b a s v

@[simp]
theorem reflectHom_apply (s v : MukaiLattice N) :
    reflectHom b s v = reflect b s v :=
  rfl

/-! ### The pairing against `s`

One computation, isolated because both the involution and the isometry proof
consume it. -/

/-- Reflecting reverses the pairing against `s` itself. This is where
`⟪s, s⟫ = -2` is spent. -/
theorem pairing_reflect_right (s : MukaiLattice N) (hs : IsSpherical b s)
    (v : MukaiLattice N) :
    pairing b (reflect b s v) s = -pairing b v s := by
  rw [reflect, pairing_add_left, pairing_smul_left, ← selfPairing_eq_pairing,
    (isSpherical_iff b s).1 hs]
  ring

/-! ### Involutivity -/

/-- **`ρ_s` is an involution** when `s` is spherical. -/
theorem reflect_reflect (s : MukaiLattice N) (hs : IsSpherical b s)
    (v : MukaiLattice N) :
    reflect b s (reflect b s v) = v := by
  conv_lhs => rw [reflect, pairing_reflect_right b s hs, reflect]
  rw [neg_smul]
  abel

theorem reflect_involutive (s : MukaiLattice N) (hs : IsSpherical b s) :
    Function.Involutive (reflect b s) :=
  reflect_reflect b s hs

theorem reflect_bijective (s : MukaiLattice N) (hs : IsSpherical b s) :
    Function.Bijective (reflect b s) :=
  (reflect_involutive b s hs).bijective

/-- `ρ_s` as a `ℤ`-linear automorphism, with itself as inverse. -/
def reflectEquiv (s : MukaiLattice N) (hs : IsSpherical b s) :
    MukaiLattice N ≃ₗ[ℤ] MukaiLattice N :=
  { reflectHom b s with
    invFun := reflect b s
    left_inv := reflect_reflect b s hs
    right_inv := reflect_reflect b s hs }

@[simp]
theorem reflectEquiv_apply (s : MukaiLattice N) (hs : IsSpherical b s)
    (v : MukaiLattice N) :
    reflectEquiv b s hs v = reflect b s v :=
  rfl

@[simp]
theorem reflectEquiv_symm_apply (s : MukaiLattice N) (hs : IsSpherical b s)
    (v : MukaiLattice N) :
    (reflectEquiv b s hs).symm v = reflect b s v :=
  rfl

/-! ### The reflection property

`reflect_self` and `reflect_of_pairing_eq_zero` are what distinguish a
reflection from an arbitrary involutive isometry: the `-1` eigenspace is
spanned by `s` and the `+1` eigenspace contains `s^⊥`. -/

/-- `ρ_s s = -s`. Needs sphericity but not symmetry. -/
@[simp]
theorem reflect_self (s : MukaiLattice N) (hs : IsSpherical b s) :
    reflect b s s = -s := by
  rw [reflect, ← selfPairing_eq_pairing, (isSpherical_iff b s).1 hs]
  module

/-- `ρ_s` fixes `s^⊥` pointwise. No hypothesis on `s` at all. -/
theorem reflect_of_pairing_eq_zero {s v : MukaiLattice N}
    (h : pairing b v s = 0) :
    reflect b s v = v := by
  rw [reflect, h, zero_smul, add_zero]

/-- The reflected vector lies in `s^⊥` exactly when the original one does. -/
theorem pairing_reflect_eq_zero_iff (s : MukaiLattice N) (hs : IsSpherical b s)
    (v : MukaiLattice N) :
    pairing b (reflect b s v) s = 0 ↔ pairing b v s = 0 := by
  rw [pairing_reflect_right b s hs, neg_eq_zero]

/-! ### Isometry

The first statements in this file to need symmetry of `b`. -/

/-- **`ρ_s` preserves the Mukai pairing.** -/
theorem pairing_reflect_reflect (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice N) (hs : IsSpherical b s) (v w : MukaiLattice N) :
    pairing b (reflect b s v) (reflect b s w) = pairing b v w := by
  have hss : pairing b s s = -2 := (isSpherical_iff b s).1 hs
  have hsw : pairing b s w = pairing b w s := pairing_comm b hb s w
  simp only [reflect, pairing_add_left, pairing_add_right, pairing_smul_left,
    pairing_smul_right, hss, hsw]
  ring

/-- `ρ_s` preserves `⟪v, v⟫`. -/
theorem selfPairing_reflect (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice N) (hs : IsSpherical b s) (v : MukaiLattice N) :
    selfPairing b (reflect b s v) = selfPairing b v := by
  simp only [selfPairing_eq_pairing]
  exact pairing_reflect_reflect b hb s hs v v

/-- `ρ_s` as an isometry of the bundled Mukai form. -/
def reflectIsometry (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice N) (hs : IsSpherical b s) :
    pairingBilin b →bᵢ pairingBilin b where
  toLinearMap := reflectHom b s
  map_app' v w := pairing_reflect_reflect b hb s hs v w

@[simp]
theorem reflectIsometry_apply (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice N) (hs : IsSpherical b s) (v : MukaiLattice N) :
    reflectIsometry b hb s hs v = reflect b s v :=
  rfl

/-! ### The distinguished classes are preserved

Corollaries of `selfPairing_reflect`, recorded separately because
`Mukai/Basic.lean` names these conditions and downstream code will rewrite with
them rather than unfolding to `selfPairing`. -/

theorem IsSpherical.reflect (hb : ∀ x y : N, b x y = b y x)
    {s : MukaiLattice N} (hs : IsSpherical b s) {v : MukaiLattice N}
    (hv : IsSpherical b v) :
    IsSpherical b (Mukai.reflect b s v) := by
  rw [isSpherical_iff, selfPairing_reflect b hb s hs]
  exact hv

theorem IsIsotropic.reflect (hb : ∀ x y : N, b x y = b y x)
    {s : MukaiLattice N} (hs : IsSpherical b s) {v : MukaiLattice N}
    (hv : IsIsotropic b v) :
    IsIsotropic b (Mukai.reflect b s v) := by
  rw [isIsotropic_iff, selfPairing_reflect b hb s hs]
  exact hv

theorem expectedDim_reflect (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice N) (hs : IsSpherical b s) (v : MukaiLattice N) :
    expectedDim b (reflect b s v) = expectedDim b v := by
  rw [expectedDim, expectedDim, selfPairing_reflect b hb s hs]

/-! ### Reflection in `-s`

`IsSpherical.neg` says `-s` is spherical whenever `s` is, so both reflections
exist; they are the same map, because the sign enters the formula twice. -/

@[simp]
theorem reflect_neg_left (s v : MukaiLattice N) :
    reflect b (-s) v = reflect b s v := by
  simp only [reflect, pairing_neg_right, neg_smul, smul_neg, neg_neg]

end Mukai
