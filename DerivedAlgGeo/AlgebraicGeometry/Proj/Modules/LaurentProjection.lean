/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.LaurentBasis
import Mathlib.Algebra.MvPolynomial.Division

/-!
# The numerator side of the sign projection

The contracting homotopy of #340 needs a **sign projection**: given a monomial denominator
`Xᵞ = X_{i₀}^c · Xᵞ'` with `γ' i₀ = 0`, a map

```
π : (A(d)_{Xᵞ})₀ → (A(d)_{Xᵞ'})₀
```

that keeps exactly the Laurent monomials whose `i₀`-exponent has not gone negative — the ones
still admissible once `X_{i₀}` is no longer inverted.

On a representative `p / (Xᵞ)ᵐ` that operation is *division by a monomial*: keep the terms of `p`
divisible by `X_{i₀}^{m·c}` and shift them down. Mathlib already has it as
`MvPolynomial.divMonomial`, so no new construction is needed and this file is the numerator-level
toolkit the projection is assembled from.

## Main statements

* `divMonomial_mem_natShift` — the degree bookkeeping: dividing off `X_{i₀}^{m·c}` moves a
  numerator for `Xᵞ` at twist `d` to a numerator for `Xᵞ'` at the same twist. The twist is
  untouched, which is what keeps `π` a map of `O(d)`-sections.
* `divMonomial_pow_mul` — **the well-definedness identity.** Raising a representative to a higher
  power of `Xᵞ` and then projecting is the same as projecting and then raising to a higher power
  of `Xᵞ'`:
  ```
  ((Xᵞ)ᵗ · p) /ᵐᵒⁿᵒᵐⁱᵃˡ X_{i₀}^{(m+t)c}  =  (Xᵞ')ᵗ · (p /ᵐᵒⁿᵒᵐⁱᵃˡ X_{i₀}^{m·c})
  ```
  Paired with `DegreeZeroLocalization.awayMk_shift`, this is exactly what makes the projection
  independent of the chosen representative: any two representatives of one element become equal
  numerators after raising both to a common denominator, and this identity says the projection
  survives that move.

## Implementation notes

`divMonomial_monomial_mul_comm` is the one genuinely new polynomial fact. A monomial factor may
be pulled out through a division only when the two monomials have **disjoint support** — the
hypothesis `∀ j, a j = 0 ∨ s j = 0`. Without it the statement is false: dividing `X_{i₀}` out of
`X_{i₀} · p` is not `X_{i₀} ·` anything. The disjointness is available here for a structural
reason, not a lucky one: the factor being pulled out is a power of `Xᵞ'`, which by hypothesis does
not involve `i₀`, while the divisor is a pure power of `X_{i₀}`.

The `γ = X_{i₀}^c · γ'` splitting is taken as a hypothesis rather than built with `Finsupp.erase`.
The caller that matters is a Čech face, which produces the two pieces separately (`c = 1` and
`γ'` the denominator of the smaller intersection) and never has to take them apart again.

`degree_eq_weight_one_apply` is a bridge, not a result. `MvPolynomial.IsHomogeneous` unfolds to a
statement about `Finsupp.weight 1` while its whole public API is stated with `Finsupp.degree`, and
the two are equal but not definitionally so.

## Tags

monomial division, homogeneous localization, projective space
-/

open MvPolynomial

namespace AlgebraicGeometry.Proj

universe u

variable {ι R : Type u} [CommRing R]

/-! ## Degree versus weight -/

/-- `Finsupp.degree` is `Finsupp.weight 1`, pointwise.

`MvPolynomial.IsHomogeneous` unfolds to the weight form while its public API is stated with
`degree`; the two are propositionally but not definitionally equal, so a proof that opens the
definition has to cross this bridge explicitly. -/
theorem degree_eq_weight_one_apply (e : ι →₀ ℕ) : Finsupp.degree e = Finsupp.weight 1 e := by
  rw [Finsupp.degree_eq_weight_one]; rfl

/-! ## Dividing by a monomial -/

/-- Dividing by a monomial drops the homogeneous degree by that monomial's degree. -/
theorem isHomogeneous_divMonomial {p : MvPolynomial ι R} {s : ι →₀ ℕ} {k : ℕ}
    (hp : p.IsHomogeneous (s.degree + k)) :
    (MvPolynomial.divMonomial p s).IsHomogeneous k := by
  intro e he
  rw [MvPolynomial.coeff_divMonomial] at he
  have h := hp he
  rw [map_add, ← degree_eq_weight_one_apply, ← degree_eq_weight_one_apply] at h
  rw [← degree_eq_weight_one_apply]
  exact Nat.add_left_cancel h

/-- Dividing off a factor that is already present leaves the rest of the division to do. -/
theorem divMonomial_monomial_mul_add (a b : ι →₀ ℕ) (x : MvPolynomial ι R) :
    MvPolynomial.divMonomial (MvPolynomial.monomial a 1 * x) (a + b) =
      MvPolynomial.divMonomial x b := by
  rw [MvPolynomial.divMonomial_add, MvPolynomial.divMonomial_monomial_mul]

/-- **A monomial factor passes through a division when their supports are disjoint.**

The hypothesis cannot be dropped: dividing `X_{i₀}` out of `X_{i₀} · p` is not `X_{i₀} ·`
anything. What disjointness buys is `a ≤ s + β ↔ a ≤ β`, so the two sides take the same branch
coefficientwise. -/
theorem divMonomial_monomial_mul_comm {a s : ι →₀ ℕ} (hd : ∀ j, a j = 0 ∨ s j = 0)
    (p : MvPolynomial ι R) :
    MvPolynomial.divMonomial (MvPolynomial.monomial a 1 * p) s =
      MvPolynomial.monomial a 1 * MvPolynomial.divMonomial p s := by
  have hiff : ∀ β : ι →₀ ℕ, a ≤ s + β ↔ a ≤ β := by
    intro β
    constructor
    · intro h j
      rcases hd j with hj | hj
      · simp [hj]
      · have := h j; simpa [hj] using this
    · intro h j; exact le_trans (h j) (by simp)
  ext β
  rw [MvPolynomial.coeff_divMonomial, MvPolynomial.coeff_monomial_mul',
    MvPolynomial.coeff_monomial_mul']
  by_cases h : a ≤ β
  · rw [if_pos ((hiff β).mpr h), if_pos h, MvPolynomial.coeff_divMonomial]
    congr 2
    ext j
    have := h j
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply]
    omega
  · rw [if_neg (fun hc => h ((hiff β).mp hc)), if_neg h]

/-! ## The projection on numerators -/

set_option maxHeartbeats 800000 in
/-- **The well-definedness identity for the sign projection.**

Raising a representative to a higher power of `Xᵞ` and then dividing off `X_{i₀}` is the same as
dividing off `X_{i₀}` and then raising to a higher power of `Xᵞ'`.

Two representatives of one element of the localization become equal numerators after raising both
to a common denominator (`awayMk_eq_awayMk_iff`), and `DegreeZeroLocalization.awayMk_shift` says
raising changes nothing downstream. This identity is the missing third fact: the projection
commutes with that raising, so it does not depend on which representative was chosen. -/
theorem divMonomial_pow_mul {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0) (m t : ℕ) (p : MvPolynomial ι R) :
    MvPolynomial.divMonomial ((MvPolynomial.monomial γ (1 : R)) ^ t * p)
        (Finsupp.single i₀ ((m + t) * c)) =
      (MvPolynomial.monomial γ' (1 : R)) ^ t *
        MvPolynomial.divMonomial p (Finsupp.single i₀ (m * c)) := by
  have hpow : (MvPolynomial.monomial γ (1 : R)) ^ t =
      MvPolynomial.monomial (Finsupp.single i₀ (t * c)) 1 *
        MvPolynomial.monomial (t • γ') 1 := by
    rw [monomial_one_pow, MvPolynomial.monomial_mul, one_mul, hγ, smul_add,
      Finsupp.smul_single, smul_eq_mul]
  have hsplit : Finsupp.single i₀ ((m + t) * c) =
      Finsupp.single i₀ (t * c) + Finsupp.single i₀ (m * c) := by
    rw [← Finsupp.single_add]
    congr 1
    ring
  have hdisj : ∀ j : ι, (t • γ') j = 0 ∨ (Finsupp.single i₀ (m * c)) j = 0 := by
    intro j
    by_cases hj : j = i₀
    · exact Or.inl (by simp [hj, hγ'])
    · exact Or.inr (by simp [Ne.symm hj])
  rw [hpow, hsplit, mul_assoc, divMonomial_monomial_mul_add,
    divMonomial_monomial_mul_comm hdisj, monomial_one_pow]

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 800000 in
/-- **The degree bookkeeping.** Dividing off `X_{i₀}^{m·c}` carries a numerator for `Xᵞ` at twist
`d` to a numerator for `Xᵞ'` at the *same* twist `d`.

Only the denominator's contribution `m • γ.degree` moves; the twist is untouched. That is what
makes the projection a map of `O(d)`-sections rather than a comparison between different
twists. -/
theorem divMonomial_mem_natShift {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') {d m : ℕ} {p : MvPolynomial ι R}
    (hp : p ∈ natShift (polynomialGrading ι R) d (m • γ.degree)) :
    MvPolynomial.divMonomial p (Finsupp.single i₀ (m * c)) ∈
      natShift (polynomialGrading ι R) d (m • γ'.degree) := by
  have hdeg : γ.degree = c + γ'.degree := by
    rw [hγ, map_add, Finsupp.degree_single]
  refine isHomogeneous_divMonomial (s := Finsupp.single i₀ (m * c)) ?_
  rw [Finsupp.degree_single]
  have hsplit : m • γ.degree + d = m * c + (m • γ'.degree + d) := by
    rw [hdeg, smul_eq_mul, smul_eq_mul]; ring
  rw [← hsplit]
  exact hp

end AlgebraicGeometry.Proj
