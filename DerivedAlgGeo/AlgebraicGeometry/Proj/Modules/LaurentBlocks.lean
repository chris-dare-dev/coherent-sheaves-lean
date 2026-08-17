/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.LaurentProjection

/-!
# The sign projections are commuting idempotents

#340's proof plan decomposes each Čech term by the *negative support* `N α = {j | α j < 0}` of
the Laurent exponent:

```
(A(d)_{Xᵞ})₀  ≅  ⨁ {F ⊆ supp γ}, W_F,    W_F = span {monomials with N α = F}
```

and then contracts each block separately, using a cone point chosen outside `F`.

The obvious way to build that decomposition is to construct a `k`-basis indexed by admissible
exponents and partition the index set. **That is not what this file does, and the shortcut is
the point.** `supp γ` is finite for every Čech denominator, so the decomposition is a *finite*
family of commuting idempotents — and the idempotents are already available:

```
signIdem = laurentFace ∘ signProjectionHom
```

keeps exactly the Laurent monomials whose `i₀`-exponent is nonnegative. Idempotency is the
retraction `signProjection_laurentFace` and nothing more; commutation for distinct variables is
`divMonomial_idem_comm`, a two-line polynomial fact. No basis, no `DirectSum`, no choice of
representative beyond the one `signProjection` already makes.

## Main statements

* `signIdem_idem` — `e ∘ e = e`, immediately from `signProjection_laurentFace`.
* `signIdem_awayMk` — the idempotent in normal form: on `p / (Xᵞ)ᵐ` it replaces `p` by
  `X_{i₀}^{m·c} · (p /ᵐᵒⁿᵒᵐⁱᵃˡ X_{i₀}^{m·c})`, i.e. it truncates away the terms whose
  `i₀`-exponent has gone negative. This is the workhorse — both other results go through it.
* `signIdem_comm` — **`e_{i₀}` and `e_{i₁}` commute for `i₀ ≠ i₁`.** With `signIdem_idem` this
  makes `{e_j}_{j ∈ supp γ}` a finite commuting family of idempotents, which is exactly the data
  a `⨁_{F ⊆ supp γ}` decomposition is assembled from.

## Implementation notes

`divMonomial_idem_comm` is where the two variables actually separate, and it needs the same
disjoint-support hypothesis as `divMonomial_monomial_mul_comm` — here supplied by `i₀ ≠ i₁`,
since each divisor is a pure power of a single variable. Both sides reduce to
`X_{s₀} · X_{s₁} · (p /ᵐᵒⁿᵒᵐⁱᵃˡ (s₀ + s₁))` via `divMonomial_add`, after which only `mul_comm`
and `add_comm` remain.

`monomial_mul_divMonomial_mem` is the degree bookkeeping that lets `signIdem` be iterated:
dividing by `X_{i₀}^{m·c}` and multiplying it straight back leaves the graded piece where it
started, so a composite of idempotents stays a legitimate numerator at the same twist.

## What this file does not assert

Nothing here builds the decomposition `⨁_F W_F` itself, or the block subcomplexes `C_F`, or any
statement about `Hⁿ`. It supplies the commuting idempotent family those are assembled from.

## Tags

idempotent, monomial division, homogeneous localization, projective space
-/

open MvPolynomial

namespace AlgebraicGeometry.Proj

universe u

variable {ι R : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## The idempotent -/

/-- **Keep exactly the Laurent monomials whose `i₀`-exponent is nonnegative.**

Project out `X_{i₀}` and put it straight back. The composite is an endomorphism of the `Xᵞ` term
rather than a comparison between two terms, which is what lets several of them be multiplied
together. -/
noncomputable def signIdem [IsDomain R] {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0) (d : ℕ) :
    DegreeZeroLocalization (polynomialGrading ι R)
        (natShift (polynomialGrading ι R) d)
        (.powers (MvPolynomial.monomial γ (1 : R))) →+
      DegreeZeroLocalization (polynomialGrading ι R)
        (natShift (polynomialGrading ι R) d)
        (.powers (MvPolynomial.monomial γ (1 : R))) :=
  (laurentFace hγ d).comp (signProjectionHom hγ hγ' d)

@[simp]
theorem signIdem_apply [IsDomain R] {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0) (d : ℕ)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (natShift (polynomialGrading ι R) d)
      (.powers (MvPolynomial.monomial γ (1 : R)))) :
    signIdem hγ hγ' d z = laurentFace hγ d (signProjection hγ d z) := rfl

/-- **The projection is idempotent.** This is exactly `signProjection_laurentFace` — putting
`X_{i₀}` back and projecting it out again is the identity — and nothing else. -/
theorem signIdem_idem [IsDomain R] {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0) (d : ℕ)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (natShift (polynomialGrading ι R) d)
      (.powers (MvPolynomial.monomial γ (1 : R)))) :
    signIdem hγ hγ' d (signIdem hγ hγ' d z) = signIdem hγ hγ' d z := by
  rw [signIdem_apply, signIdem_apply, signProjection_laurentFace hγ hγ']

/-! ## Normal form and iterability -/

/-- Dividing by `X_{i₀}^{m·c}` and multiplying it back leaves the graded piece alone.

This is what lets `signIdem` be iterated: a composite of idempotents is still a legitimate
numerator over `(Xᵞ)ᵐ` at the same twist. -/
theorem monomial_mul_divMonomial_mem {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') {d m : ℕ} {p : MvPolynomial ι R}
    (hp : p ∈ natShift (polynomialGrading ι R) d (m • γ.degree)) :
    MvPolynomial.monomial (Finsupp.single i₀ (m * c)) (1 : R) *
      MvPolynomial.divMonomial p (Finsupp.single i₀ (m * c)) ∈
      natShift (polynomialGrading ι R) d (m • γ.degree) := by
  have hdiv := divMonomial_mem_natShift hγ hp
  have h1 : (MvPolynomial.monomial (Finsupp.single i₀ (m * c)) (1 : R)).IsHomogeneous (m * c) :=
    MvPolynomial.isHomogeneous_monomial 1 (by rw [Finsupp.degree_single])
  have h2 : (MvPolynomial.divMonomial p (Finsupp.single i₀ (m * c))).IsHomogeneous
      (m • γ'.degree + d) := hdiv
  have h3 := h1.mul h2
  have hdeg : γ.degree = c + γ'.degree := by rw [hγ, map_add, Finsupp.degree_single]
  have hd2 : m * c + (m • γ'.degree + d) = m • γ.degree + d := by
    rw [hdeg]; simp only [smul_eq_mul]; ring
  rw [hd2] at h3
  exact h3

set_option maxHeartbeats 1200000 in
/-- **The idempotent in `awayMk` normal form.** On `p / (Xᵞ)ᵐ` it truncates the numerator to the
terms divisible by `X_{i₀}^{m·c}` — precisely the Laurent monomials whose `i₀`-exponent has not
gone negative — and leaves the exponent alone.

Every other statement about `signIdem` goes through this one. -/
theorem signIdem_awayMk [IsDomain R] {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0) {d m : ℕ} {p : MvPolynomial ι R}
    (hp : p ∈ natShift (polynomialGrading ι R) d (m • γ.degree))
    (hres : MvPolynomial.monomial (Finsupp.single i₀ (m * c)) (1 : R) *
      MvPolynomial.divMonomial p (Finsupp.single i₀ (m * c)) ∈
      natShift (polynomialGrading ι R) d (m • γ.degree)) :
    signIdem hγ hγ' d (DegreeZeroLocalization.awayMk
        (𝓜 := natShift (polynomialGrading ι R) d)
        (monomial_one_mem_polynomialGrading (R := R) γ) m p hp) =
      DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
        (monomial_one_mem_polynomialGrading (R := R) γ) m
        (MvPolynomial.monomial (Finsupp.single i₀ (m * c)) (1 : R) *
          MvPolynomial.divMonomial p (Finsupp.single i₀ (m * c))) hres := by
  have hdeg : γ.degree = c + γ'.degree := by rw [hγ, map_add, Finsupp.degree_single]
  have hmono : (MvPolynomial.monomial (Finsupp.single i₀ c) (1 : R)) ^ m =
      MvPolynomial.monomial (Finsupp.single i₀ (m * c)) 1 := by
    rw [monomial_one_pow, Finsupp.smul_single, smul_eq_mul]
  have hres2 : (MvPolynomial.monomial (Finsupp.single i₀ c) (1 : R)) ^ m •
      MvPolynomial.divMonomial p (Finsupp.single i₀ (m * c)) ∈
      natShift (polynomialGrading ι R) d (m • (c + γ'.degree)) := by
    rw [hmono, smul_eq_mul, ← hdeg]; exact hres
  rw [signIdem_apply, signProjection_awayMk hγ hγ', laurentFace_awayMk hγ _ hres2,
    DegreeZeroLocalization.awayMk_deg_congr hdeg.symm (monomial_mem_add_degree hγ)
      (monomial_one_mem_polynomialGrading (R := R) γ) m _ hres2 (by rw [hdeg]; exact hres2)]
  have hcongr : ∀ (a b : MvPolynomial ι R)
      (ha : a ∈ natShift (polynomialGrading ι R) d (m • γ.degree))
      (hb : b ∈ natShift (polynomialGrading ι R) d (m • γ.degree)), a = b →
      DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
          (monomial_one_mem_polynomialGrading (R := R) γ) m a ha =
        DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
          (monomial_one_mem_polynomialGrading (R := R) γ) m b hb := by
    rintro a b ha hb rfl; rfl
  exact hcongr _ _ _ hres (by rw [hmono, smul_eq_mul])

/-! ## Commutation -/

/-- Two truncations at distinct variables commute.

Both sides reduce to `X_{s₀} · X_{s₁} · (p /ᵐᵒⁿᵒᵐⁱᵃˡ (s₀ + s₁))`: `divMonomial_monomial_mul_comm`
pulls each monomial through the other division — legitimate because the two divisors have
disjoint support — and `divMonomial_add` merges the two divisions. What is left is `mul_comm`
and `add_comm`. -/
theorem divMonomial_idem_comm {s₀ s₁ : ι →₀ ℕ} (hd : ∀ j, s₀ j = 0 ∨ s₁ j = 0)
    (p : MvPolynomial ι R) :
    MvPolynomial.monomial s₁ (1 : R) * MvPolynomial.divMonomial
        (MvPolynomial.monomial s₀ (1 : R) * MvPolynomial.divMonomial p s₀) s₁ =
      MvPolynomial.monomial s₀ (1 : R) * MvPolynomial.divMonomial
        (MvPolynomial.monomial s₁ (1 : R) * MvPolynomial.divMonomial p s₁) s₀ := by
  rw [divMonomial_monomial_mul_comm hd, divMonomial_monomial_mul_comm
        (fun j => (hd j).symm),
    ← MvPolynomial.divMonomial_add, ← MvPolynomial.divMonomial_add,
    ← mul_assoc, ← mul_assoc, mul_comm (MvPolynomial.monomial s₁ (1 : R)),
    add_comm s₁ s₀]

set_option maxHeartbeats 1600000 in
/-- **The sign projections at distinct variables commute.**

With `signIdem_idem` this makes `{e_j}_{j ∈ supp γ}` a finite commuting family of idempotents.
`supp γ` is finite for every Čech denominator, so the `⨁_{F ⊆ supp γ}` decomposition of #340's
proof plan is assembled from this family by ordinary idempotent algebra — no basis and no
`DirectSum` construction on the localization is needed.

The hypothesis is only `i₀ ≠ i₁`; the two splittings of `γ` are otherwise unrelated, which is
what a Čech denominator supplies (each variable it inverts gives one splitting). -/
theorem signIdem_comm [IsDomain R] {γ γ₀ γ₁ : ι →₀ ℕ} {i₀ i₁ : ι} {c₀ c₁ : ℕ}
    (hγ₀ : γ = Finsupp.single i₀ c₀ + γ₀) (hγ₀' : γ₀ i₀ = 0)
    (hγ₁ : γ = Finsupp.single i₁ c₁ + γ₁) (hγ₁' : γ₁ i₁ = 0) (hne : i₀ ≠ i₁) (d : ℕ)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (natShift (polynomialGrading ι R) d)
      (.powers (MvPolynomial.monomial γ (1 : R)))) :
    signIdem hγ₀ hγ₀' d (signIdem hγ₁ hγ₁' d z) =
      signIdem hγ₁ hγ₁' d (signIdem hγ₀ hγ₀' d z) := by
  obtain ⟨m, p, hp, rfl⟩ :=
    DegreeZeroLocalization.exists_awayMk (monomial_one_mem_polynomialGrading (R := R) γ)
      (monomial_one_pow_ne_zero γ) z
  have hdisj : ∀ j : ι, (Finsupp.single i₀ (m * c₀)) j = 0 ∨
      (Finsupp.single i₁ (m * c₁)) j = 0 := by
    intro j
    by_cases hj : j = i₀
    · exact Or.inr (by simp [hj, Ne.symm hne])
    · exact Or.inl (by simp [Ne.symm hj])
  rw [signIdem_awayMk hγ₁ hγ₁' hp (monomial_mul_divMonomial_mem hγ₁ hp),
    signIdem_awayMk hγ₀ hγ₀' _
      (monomial_mul_divMonomial_mem hγ₀ (monomial_mul_divMonomial_mem hγ₁ hp)),
    signIdem_awayMk hγ₀ hγ₀' hp (monomial_mul_divMonomial_mem hγ₀ hp),
    signIdem_awayMk hγ₁ hγ₁' _
      (monomial_mul_divMonomial_mem hγ₁ (monomial_mul_divMonomial_mem hγ₀ hp))]
  have hcongr : ∀ (a b : MvPolynomial ι R)
      (ha : a ∈ natShift (polynomialGrading ι R) d (m • γ.degree))
      (hb : b ∈ natShift (polynomialGrading ι R) d (m • γ.degree)), a = b →
      DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
          (monomial_one_mem_polynomialGrading (R := R) γ) m a ha =
        DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
          (monomial_one_mem_polynomialGrading (R := R) γ) m b hb := by
    rintro a b ha hb rfl; rfl
  exact hcongr _ _ _ _ (divMonomial_idem_comm hdisj p).symm

end AlgebraicGeometry.Proj
