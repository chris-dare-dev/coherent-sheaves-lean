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
* `signProjection` — **the projection itself**, with `signProjection_awayMk` the equation that
  pins it down and `signProjection_laurentFace` the retraction `π ∘ ι = id`.
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

/-! ## The projection itself

The numerator operation descends to a map on the localization. A representative is packaged as
`AwayRep`; `AwayRep.frac_project_congr` says two representatives of one element project to the
same fraction, and `signProjection` is the resulting map, chosen through `Exists.choose` and
pinned by `signProjection_awayMk`. -/

/-- A representative `p / (Xᵞ)ᵐ` of a degree-zero fraction at twist `d`. -/
structure AwayRep (ι R : Type u) [CommRing R] (γ : ι →₀ ℕ) (d : ℕ) where
  /-- The exponent of the denominator. -/
  pow : ℕ
  /-- The numerator. -/
  num : MvPolynomial ι R
  /-- The numerator sits in the graded piece the denominator forces. -/
  num_mem : num ∈ natShift (polynomialGrading ι R) d (pow • γ.degree)

/-- The fraction a representative names. -/
noncomputable def AwayRep.frac {γ : ι →₀ ℕ} {d : ℕ} (r : AwayRep ι R γ d) :
    DegreeZeroLocalization (polynomialGrading ι R)
      (natShift (polynomialGrading ι R) d) (.powers (MvPolynomial.monomial γ (1 : R))) :=
  DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
    (monomial_one_mem_polynomialGrading (R := R) γ) r.pow r.num r.num_mem

/-- Every fraction has a representative — this is `exists_awayMk`, repackaged. -/
theorem AwayRep.frac_surjective [Nontrivial R] (γ : ι →₀ ℕ) (d : ℕ)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (natShift (polynomialGrading ι R) d) (.powers (MvPolynomial.monomial γ (1 : R)))) :
    ∃ r : AwayRep ι R γ d, r.frac = z := by
  obtain ⟨m, p, hp, rfl⟩ :=
    DegreeZeroLocalization.exists_awayMk (monomial_one_mem_polynomialGrading (R := R) γ)
      (monomial_one_pow_ne_zero γ) z
  exact ⟨⟨m, p, hp⟩, rfl⟩

/-- The projected representative: divide the numerator by `X_{i₀}^{m·c}`, keep the exponent. -/
noncomputable def AwayRep.project {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') {d : ℕ} (r : AwayRep ι R γ d) : AwayRep ι R γ' d where
  pow := r.pow
  num := MvPolynomial.divMonomial r.num (Finsupp.single i₀ (r.pow * c))
  num_mem := divMonomial_mem_natShift hγ r.num_mem

/-- Raising a representative by `(Xᵞ)ᵗ` keeps it a legitimate numerator. -/
theorem AwayRep.pow_mul_num_mem {γ : ι →₀ ℕ} {d : ℕ} (r : AwayRep ι R γ d) (t : ℕ) :
    ((MvPolynomial.monomial γ (1 : R)) ^ t * r.num) ∈
      natShift (polynomialGrading ι R) d ((r.pow + t) • γ.degree) := by
  have h1 : ((MvPolynomial.monomial γ (1 : R)) ^ t).IsHomogeneous (t * γ.degree) := by
    rw [monomial_one_pow]
    exact MvPolynomial.isHomogeneous_monomial 1 (by rw [map_nsmul, smul_eq_mul])
  have h2 : (r.num).IsHomogeneous (r.pow • γ.degree + d) := r.num_mem
  have h3 := h1.mul h2
  have hd : t * γ.degree + (r.pow • γ.degree + d) = (r.pow + t) • γ.degree + d := by
    simp only [smul_eq_mul]; ring
  rw [hd] at h3
  exact h3

set_option maxHeartbeats 1200000 in
/-- Projecting a representative is the same as raising it first and then projecting.

This is `divMonomial_pow_mul` on the numerator and `awayMk_shift` on the fraction, and it is the
only place either is used. Well-definedness follows immediately: it lets both representatives of
one element be moved to the *same* exponent before they are compared. -/
theorem AwayRep.frac_project_raise {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0) {d : ℕ}
    (r : AwayRep ι R γ d) (t : ℕ) :
    (r.project hγ).frac =
      DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
        (monomial_one_mem_polynomialGrading (R := R) γ') (r.pow + t)
        (MvPolynomial.divMonomial ((MvPolynomial.monomial γ (1 : R)) ^ t * r.num)
          (Finsupp.single i₀ ((r.pow + t) * c)))
        (divMonomial_mem_natShift hγ (r.pow_mul_num_mem t)) := by
  have hnum := divMonomial_pow_mul hγ hγ' r.pow t r.num
  have hmem2 : (MvPolynomial.monomial γ' (1 : R)) ^ t •
      MvPolynomial.divMonomial r.num (Finsupp.single i₀ (r.pow * c)) ∈
      natShift (polynomialGrading ι R) d ((r.pow + t) • γ'.degree) := by
    simp only [smul_eq_mul, ← hnum]
    exact divMonomial_mem_natShift hγ (r.pow_mul_num_mem t)
  have hcongr : ∀ (n : ℕ) (a b : MvPolynomial ι R)
      (ha : a ∈ natShift (polynomialGrading ι R) d (n • γ'.degree))
      (hb : b ∈ natShift (polynomialGrading ι R) d (n • γ'.degree)), a = b →
      DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
          (monomial_one_mem_polynomialGrading (R := R) γ') n a ha =
        DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
          (monomial_one_mem_polynomialGrading (R := R) γ') n b hb := by
    rintro n a b ha hb rfl; rfl
  refine Eq.symm (Eq.trans (hcongr (r.pow + t) _ _ _ hmem2 hnum) ?_)
  exact DegreeZeroLocalization.awayMk_shift
    (monomial_one_mem_polynomialGrading (R := R) γ') r.pow t
    (MvPolynomial.divMonomial r.num (Finsupp.single i₀ (r.pow * c)))
    (divMonomial_mem_natShift hγ r.num_mem) hmem2

set_option maxHeartbeats 1200000 in
/-- **Well-definedness.** Two representatives of one fraction project to the same fraction.

`awayMk_eq_awayMk_iff` turns the hypothesis into a cross-multiplication of numerators, and
`frac_project_raise` moves both projections to the common exponent `r₁.pow + r₂.pow` where that
cross-multiplication is literally the equality of numerators. -/
theorem AwayRep.frac_project_congr [IsDomain R] {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0) {d : ℕ}
    {r₁ r₂ : AwayRep ι R γ d} (h : r₁.frac = r₂.frac) :
    (r₁.project hγ).frac = (r₂.project hγ).frac := by
  have hcross : (MvPolynomial.monomial γ (1 : R)) ^ r₂.pow * r₁.num =
      (MvPolynomial.monomial γ (1 : R)) ^ r₁.pow * r₂.num := by
    have hx := (DegreeZeroLocalization.awayMk_eq_awayMk_iff
      (monomial_one_mem_polynomialGrading (R := R) γ)
      (monomial_one_ne_zero (R := R) γ) r₁.num_mem r₂.num_mem).mp h
    simpa [smul_eq_mul] using hx
  have hgen : ∀ (n₁ n₂ : ℕ) (a b : MvPolynomial ι R)
      (ha : a ∈ natShift (polynomialGrading ι R) d (n₁ • γ'.degree))
      (hb : b ∈ natShift (polynomialGrading ι R) d (n₂ • γ'.degree)),
      n₁ = n₂ → a = b →
      DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
          (monomial_one_mem_polynomialGrading (R := R) γ') n₁ a ha =
        DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
          (monomial_one_mem_polynomialGrading (R := R) γ') n₂ b hb := by
    rintro n₁ n₂ a b ha hb rfl rfl; rfl
  refine (r₁.frac_project_raise hγ hγ' r₂.pow).trans
    (Eq.trans (hgen _ _ _ _ _ _ (Nat.add_comm _ _) ?_)
      (r₂.frac_project_raise hγ hγ' r₁.pow).symm)
  rw [Nat.add_comm r₁.pow r₂.pow, hcross]

/-- **The sign projection**, as a map on the localization.

Defined by choosing a representative; `signProjection_awayMk` is the equation that pins it down
and is what every caller should use. The hypothesis `γ' i₀ = 0` is not needed to *make* the
definition — only to make it independent of the choice — so it is required by the equations rather
than by the definition. -/
noncomputable def signProjection [IsDomain R] {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (d : ℕ)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (natShift (polynomialGrading ι R) d) (.powers (MvPolynomial.monomial γ (1 : R)))) :
    DegreeZeroLocalization (polynomialGrading ι R)
      (natShift (polynomialGrading ι R) d) (.powers (MvPolynomial.monomial γ' (1 : R))) :=
  ((AwayRep.frac_surjective γ d z).choose.project hγ).frac

theorem signProjection_frac [IsDomain R] {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0) {d : ℕ} (r : AwayRep ι R γ d) :
    signProjection hγ d r.frac = (r.project hγ).frac :=
  AwayRep.frac_project_congr hγ hγ' (AwayRep.frac_surjective γ d r.frac).choose_spec

/-- **The defining equation of the sign projection**: on a representative it divides the numerator
by `X_{i₀}^{m·c}` and keeps the exponent. -/
theorem signProjection_awayMk [IsDomain R] {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0) {d m : ℕ} {p : MvPolynomial ι R}
    (hp : p ∈ natShift (polynomialGrading ι R) d (m • γ.degree)) :
    signProjection hγ d
        (DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
          (monomial_one_mem_polynomialGrading (R := R) γ) m p hp) =
      DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
        (monomial_one_mem_polynomialGrading (R := R) γ') m
        (MvPolynomial.divMonomial p (Finsupp.single i₀ (m * c)))
        (divMonomial_mem_natShift hγ hp) :=
  signProjection_frac hγ hγ' ⟨m, p, hp⟩

/-! ## The projection retracts the face inclusion -/

theorem monomial_single_mem (i₀ : ι) (c : ℕ) :
    (MvPolynomial.monomial (Finsupp.single i₀ c) (1 : R)) ∈ polynomialGrading ι R c := by
  have h := monomial_one_mem_polynomialGrading (R := R) (Finsupp.single i₀ c)
  rwa [Finsupp.degree_single] at h

theorem laurentFace_mul {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') :
    (MvPolynomial.monomial γ' (1 : R)) * MvPolynomial.monomial (Finsupp.single i₀ c) 1 =
      MvPolynomial.monomial γ 1 := by
  rw [MvPolynomial.monomial_mul, one_mul, hγ, add_comm]

theorem monomial_mem_add_degree {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') :
    (MvPolynomial.monomial γ (1 : R)) ∈ polynomialGrading ι R (c + γ'.degree) := by
  have h := monomial_one_mem_polynomialGrading (R := R) γ
  have hd : γ.degree = c + γ'.degree := by rw [hγ, map_add, Finsupp.degree_single]
  rwa [hd] at h

/-- The face inclusion `(A(d)_{Xᵞ'})₀ → (A(d)_{Xᵞ})₀`, in the shape the sign projection
retracts. This is `DegreeZeroLocalization.faceMap` at `g₁ * h = g₂` with `h = X_{i₀}^c`, which is
exactly the Čech face of #340's complex. -/
noncomputable def laurentFace {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (d : ℕ) :
    DegreeZeroLocalization (polynomialGrading ι R)
        (natShift (polynomialGrading ι R) d) (.powers (MvPolynomial.monomial γ' (1 : R))) →+
      DegreeZeroLocalization (polynomialGrading ι R)
        (natShift (polynomialGrading ι R) d) (.powers (MvPolynomial.monomial γ (1 : R))) :=
  DegreeZeroLocalization.faceMap (𝓜 := natShift (polynomialGrading ι R) d)
    (monomial_single_mem i₀ c)
    ⟨1, by show (MvPolynomial.monomial γ (1 : R)) ^ 1 = _; rw [pow_one, laurentFace_mul hγ]⟩
    (laurentFace_mul hγ)

set_option maxHeartbeats 1200000 in
/-- The face inclusion in `awayMk` normal form: it multiplies the numerator by
`X_{i₀}^{m·c}`. -/
theorem laurentFace_awayMk {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') {d m : ℕ} {q : MvPolynomial ι R}
    (hq : q ∈ natShift (polynomialGrading ι R) d (m • γ'.degree))
    (hres : (MvPolynomial.monomial (Finsupp.single i₀ c) (1 : R)) ^ m • q ∈
      natShift (polynomialGrading ι R) d (m • (c + γ'.degree))) :
    laurentFace hγ d (DegreeZeroLocalization.awayMk
        (𝓜 := natShift (polynomialGrading ι R) d)
        (monomial_one_mem_polynomialGrading (R := R) γ') m q hq) =
      DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
        (monomial_mem_add_degree hγ) m
        ((MvPolynomial.monomial (Finsupp.single i₀ c) (1 : R)) ^ m • q) hres :=
  DegreeZeroLocalization.faceMap_awayMk _ (monomial_one_mem_polynomialGrading (R := R) γ') _ _
    (monomial_mem_add_degree hγ) m q hq hres

set_option maxHeartbeats 1200000 in
/-- **The sign projection retracts the face inclusion**: `π ∘ ι = id`.

This is the first of the two properties #340's homotopy consumes. On a representative the face
multiplies the numerator by `X_{i₀}^{m·c}` and the projection divides it straight back out
(`divMonomial_monomial_mul`), so nothing survives to check — the content is all in the degree
bookkeeping, and in `awayMk_deg_congr` reconciling the two names `γ.degree` and `c + γ'.degree`
for the same natural number. -/
theorem signProjection_laurentFace [IsDomain R] {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0) (d : ℕ)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (natShift (polynomialGrading ι R) d) (.powers (MvPolynomial.monomial γ' (1 : R)))) :
    signProjection hγ d (laurentFace hγ d z) = z := by
  obtain ⟨m, q, hq, rfl⟩ :=
    DegreeZeroLocalization.exists_awayMk (monomial_one_mem_polynomialGrading (R := R) γ')
      (monomial_one_pow_ne_zero γ') z
  have hdeg : γ.degree = c + γ'.degree := by rw [hγ, map_add, Finsupp.degree_single]
  have hmono : (MvPolynomial.monomial (Finsupp.single i₀ c) (1 : R)) ^ m =
      MvPolynomial.monomial (Finsupp.single i₀ (m * c)) 1 := by
    rw [monomial_one_pow, Finsupp.smul_single, smul_eq_mul]
  have hres : (MvPolynomial.monomial (Finsupp.single i₀ c) (1 : R)) ^ m • q ∈
      natShift (polynomialGrading ι R) d (m • (c + γ'.degree)) := by
    have h1 : ((MvPolynomial.monomial (Finsupp.single i₀ c) (1 : R)) ^ m).IsHomogeneous
        (m * c) := by
      rw [hmono]
      exact MvPolynomial.isHomogeneous_monomial 1 (by rw [Finsupp.degree_single])
    have h2 : (q : MvPolynomial ι R).IsHomogeneous (m • γ'.degree + d) := hq
    have h3 := h1.mul h2
    have hd2 : m * c + (m • γ'.degree + d) = m • (c + γ'.degree) + d := by
      simp only [smul_eq_mul]; ring
    rw [hd2] at h3
    exact h3
  rw [laurentFace_awayMk hγ hq hres,
    DegreeZeroLocalization.awayMk_deg_congr hdeg.symm (monomial_mem_add_degree hγ)
      (monomial_one_mem_polynomialGrading (R := R) γ) m _ hres
      (by rw [hdeg]; exact hres),
    signProjection_awayMk hγ hγ']
  have hnum : MvPolynomial.divMonomial
      ((MvPolynomial.monomial (Finsupp.single i₀ c) (1 : R)) ^ m • q)
      (Finsupp.single i₀ (m * c)) = q := by
    rw [hmono, smul_eq_mul, MvPolynomial.divMonomial_monomial_mul]
  have hcongr : ∀ (a b : MvPolynomial ι R)
      (ha : a ∈ natShift (polynomialGrading ι R) d (m • γ'.degree))
      (hb : b ∈ natShift (polynomialGrading ι R) d (m • γ'.degree)), a = b →
      DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
          (monomial_one_mem_polynomialGrading (R := R) γ') m a ha =
        DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
          (monomial_one_mem_polynomialGrading (R := R) γ') m b hb := by
    rintro a b ha hb rfl; rfl
  exact hcongr _ _ _ hq hnum

end AlgebraicGeometry.Proj
