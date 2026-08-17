/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.Finiteness

/-!
# Laurent exponents of monomial fractions

A degree-zero fraction away from a monomial `Xᵞ` has, by `DegreeZeroLocalization.exists_awayMk`,
the normal form `p / (Xᵞ)ᵐ`. When the numerator is itself a monomial `Xᵝ`, the fraction is
determined by a single Laurent exponent

```
laurentExponent γ m β = β - m • γ  :  ι →₀ ℤ
```

with negative entries allowed exactly on the variables `Xᵞ` inverts. This file constructs that
exponent and proves the three facts that make it an index: it determines the fraction, its
`Finsupp.degree` is the twist `d`, and it is nonnegative off the support of `γ`.

## Main definitions

* `natToIntExponent` — an exponent vector read in `ℤ`;
* `laurentExponent` — the Laurent exponent `β - m • γ` of the fraction `Xᵝ / (Xᵞ)ᵐ`.

## Main statements

* `awayMk_monomial_eq_iff_laurentExponent` — **two monomial fractions over powers of `Xᵞ` are
  equal exactly when their Laurent exponents agree.** This is what makes the exponent an index
  rather than a convenience.
* `degree_laurentExponent` — the exponent has total degree `d`, the twist, with no dependence on
  `m`. Raising the denominator moves `β` and `m • γ` together, so this is the invariant that
  survives.
* `laurentExponent_nonneg_of_apply_eq_zero` — off the support of `γ` the exponent is
  nonnegative. Together with the previous statement this is the index set
  `{α | Finsupp.degree α = d ∧ ∀ j ∉ γ.support, 0 ≤ α j}` that #491's basis is indexed by.

## Implementation notes

The equality criterion descends from `DegreeZeroLocalization.awayMk_eq_awayMk_iff`, which is
where the domain hypothesis is spent, to `MvPolynomial.monomial_eq_monomial_iff`. Only the
`IsDomain R` instance is needed: `Module.IsTorsionFree R R` is already an instance, so the
polynomial case supplies nothing by hand.

`laurentExponent` is stated with `m` and `β` separate rather than packaged, because the caller
that matters — a Čech cochain — produces them separately from `exists_awayMk` and never has the
pair in hand.

## Tags

Laurent monomial, homogeneous localization, projective space
-/

open DirectSum SetLike MvPolynomial

namespace AlgebraicGeometry.Proj

universe u

/-! ## Exponent vectors in `ℤ` -/

variable {ι : Type u}

/-- An exponent vector read in `ℤ`, so that an inverted variable can carry a negative
exponent. -/
noncomputable def natToIntExponent : (ι →₀ ℕ) →+ (ι →₀ ℤ) :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

theorem natToIntExponent_injective :
    Function.Injective (natToIntExponent (ι := ι)) := fun _ _ h =>
  Finsupp.mapRange_injective (Nat.cast) Nat.cast_zero Nat.cast_injective h

/-- Reading an exponent vector in `ℤ` does not change its total degree. -/
theorem degree_natToIntExponent (β : ι →₀ ℕ) :
    (natToIntExponent β).degree = (β.degree : ℤ) := by
  classical
  induction β using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | single a b => simp [natToIntExponent, Finsupp.degree_single]

/-! ## The Laurent exponent of a monomial fraction -/

/-- The Laurent exponent of the monomial fraction `Xᵝ / (Xᵞ)ᵐ`.

Entries are negative exactly where `m • γ` exceeds `β`, which can only happen on the support of
`γ` — the variables the localization inverts. -/
noncomputable def laurentExponent (γ : ι →₀ ℕ) (m : ℕ) (β : ι →₀ ℕ) : ι →₀ ℤ :=
  natToIntExponent β - m • natToIntExponent γ

@[simp]
theorem laurentExponent_apply (γ : ι →₀ ℕ) (m : ℕ) (β : ι →₀ ℕ) (j : ι) :
    laurentExponent γ m β j = (β j : ℤ) - m * (γ j : ℤ) := by
  simp [laurentExponent, natToIntExponent]

/-- Two monomial fractions over powers of `Xᵞ` have the same Laurent exponent exactly when their
numerators agree after clearing denominators. -/
theorem laurentExponent_eq_iff (γ : ι →₀ ℕ) (m m' : ℕ) (β β' : ι →₀ ℕ) :
    laurentExponent γ m β = laurentExponent γ m' β' ↔ m' • γ + β = m • γ + β' := by
  rw [laurentExponent, laurentExponent, sub_eq_sub_iff_add_eq_add,
    ← map_nsmul, ← map_nsmul, ← map_add, ← map_add,
    Function.Injective.eq_iff natToIntExponent_injective]
  constructor
  · intro h; rw [add_comm (m' • γ), add_comm (m • γ)]; exact h
  · intro h; rw [add_comm β, add_comm β']; exact h

/-- **The Laurent exponent has total degree the twist.**

The numerator of a degree-`d` fraction over `(Xᵞ)ᵐ` has degree `m • γ.degree + d`, and the
exponent subtracts exactly the `m • γ.degree` back off. So `m` disappears: the total degree is
`d` for every representative, which is what lets the exponent index a `d`-graded piece. -/
theorem degree_laurentExponent (γ β : ι →₀ ℕ) (m d : ℕ)
    (hβ : β.degree = m • γ.degree + d) :
    (laurentExponent γ m β).degree = d := by
  rw [laurentExponent, map_sub, map_nsmul, degree_natToIntExponent,
    degree_natToIntExponent, hβ, nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

/-- Off the support of `γ` the Laurent exponent is nonnegative: a variable the localization does
not invert cannot acquire a negative exponent. -/
theorem laurentExponent_nonneg_of_apply_eq_zero (γ : ι →₀ ℕ) (m : ℕ) (β : ι →₀ ℕ) {j : ι}
    (hj : γ j = 0) : 0 ≤ laurentExponent γ m β j := by
  simp [hj]

/-! ## Monomials as homogeneous denominators and numerators -/

variable {R : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `Xᵞ` is homogeneous of degree `γ.degree`, which is the certificate `awayMk` consumes. -/
theorem monomial_one_mem_polynomialGrading (γ : ι →₀ ℕ) :
    (MvPolynomial.monomial γ (1 : R)) ∈ polynomialGrading ι R γ.degree :=
  MvPolynomial.isHomogeneous_monomial 1 rfl

theorem monomial_one_pow (γ : ι →₀ ℕ) (m : ℕ) :
    (MvPolynomial.monomial γ (1 : R)) ^ m = MvPolynomial.monomial (m • γ) 1 := by
  rw [MvPolynomial.monomial_pow, one_pow]

theorem monomial_one_ne_zero [Nontrivial R] (γ : ι →₀ ℕ) :
    (MvPolynomial.monomial γ (1 : R)) ≠ 0 := by
  simp

/-- A monomial of the right total degree is a legitimate numerator over `(Xᵞ)ᵐ` for the twist
`d`. -/
theorem monomial_mem_natShift (γ β : ι →₀ ℕ) (d m : ℕ)
    (hβ : β.degree = m • γ.degree + d) :
    (MvPolynomial.monomial β (1 : R)) ∈
      natShift (polynomialGrading ι R) d (m • γ.degree) :=
  MvPolynomial.isHomogeneous_monomial 1 hβ

/-! ## The equality criterion -/

set_option maxHeartbeats 800000 in
/-- Two monomial fractions over powers of `Xᵞ` are equal exactly when they cross-multiply to the
same monomial. This is `awayMk_eq_awayMk_iff` followed by `monomial_eq_monomial_iff`; the
coefficient side of the latter is discharged by `1 ≠ 0`. -/
theorem awayMk_monomial_eq_iff [IsDomain R] (γ : ι →₀ ℕ) (d : ℕ) {m m' : ℕ} {β β' : ι →₀ ℕ}
    (hβ : (MvPolynomial.monomial β (1 : R)) ∈
      natShift (polynomialGrading ι R) d (m • γ.degree))
    (hβ' : (MvPolynomial.monomial β' (1 : R)) ∈
      natShift (polynomialGrading ι R) d (m' • γ.degree)) :
    DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
        (monomial_one_mem_polynomialGrading (R := R) γ) m (MvPolynomial.monomial β 1) hβ =
      DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
        (monomial_one_mem_polynomialGrading (R := R) γ) m' (MvPolynomial.monomial β' 1) hβ' ↔
      m' • γ + β = m • γ + β' := by
  rw [DegreeZeroLocalization.awayMk_eq_awayMk_iff _ (monomial_one_ne_zero (R := R) γ),
    smul_eq_mul, smul_eq_mul, monomial_one_pow, monomial_one_pow,
    MvPolynomial.monomial_mul, MvPolynomial.monomial_mul, one_mul,
    MvPolynomial.monomial_eq_monomial_iff]
  simp

set_option maxHeartbeats 800000 in
/-- **The Laurent exponent is a complete invariant of a monomial fraction.**

This is the statement #491's basis is built on: the assignment `(m, β) ↦ β - m • γ` separates
distinct fractions and identifies the ones that only differ by a common denominator. Combined
with `degree_laurentExponent` and `laurentExponent_nonneg_of_apply_eq_zero`, it says the monomial
fractions of the twist `d` are indexed by
`{α : ι →₀ ℤ | α.degree = d ∧ ∀ j, γ j = 0 → 0 ≤ α j}`. -/
theorem awayMk_monomial_eq_iff_laurentExponent [IsDomain R] (γ : ι →₀ ℕ) (d : ℕ) {m m' : ℕ}
    {β β' : ι →₀ ℕ}
    (hβ : (MvPolynomial.monomial β (1 : R)) ∈
      natShift (polynomialGrading ι R) d (m • γ.degree))
    (hβ' : (MvPolynomial.monomial β' (1 : R)) ∈
      natShift (polynomialGrading ι R) d (m' • γ.degree)) :
    DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
        (monomial_one_mem_polynomialGrading (R := R) γ) m (MvPolynomial.monomial β 1) hβ =
      DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
        (monomial_one_mem_polynomialGrading (R := R) γ) m' (MvPolynomial.monomial β' 1) hβ' ↔
      laurentExponent γ m β = laurentExponent γ m' β' :=
  (awayMk_monomial_eq_iff γ d hβ hβ').trans (laurentExponent_eq_iff γ m m' β β').symm

end AlgebraicGeometry.Proj
