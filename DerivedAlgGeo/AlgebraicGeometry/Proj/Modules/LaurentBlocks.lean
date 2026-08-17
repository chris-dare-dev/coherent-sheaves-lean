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
  makes `{e_j}` a commuting family of idempotents.
* `signIdemAt` — the same idempotent with the splitting supplied uniformly by `Finsupp.erase`,
  so it is indexed by a variable rather than by a splitting.
* `signIdemAt_eq_self_of_apply_eq_zero` — at a variable the denominator does not invert, the
  idempotent is the identity. This is what makes the peeling induction terminate degreewise.
* `signIdem_laurentFace_same` — the projection commutes with the face that inserts `X_{i₀}`
  itself, the one case `signProjection_laurentFace_comm` cannot be instantiated at.

## Implementation notes

`divMonomial_idem_comm` is where the two variables actually separate, and it needs the same
disjoint-support hypothesis as `divMonomial_monomial_mul_comm` — here supplied by `i₀ ≠ i₁`,
since each divisor is a pure power of a single variable. Both sides reduce to
`X_{s₀} · X_{s₁} · (p /ᵐᵒⁿᵒᵐⁱᵃˡ (s₀ + s₁))` via `divMonomial_add`, after which only `mul_comm`
and `add_comm` remain.

`monomial_mul_divMonomial_mem` is the degree bookkeeping that lets `signIdem` be iterated:
dividing by `X_{i₀}^{m·c}` and multiplying it straight back leaves the graded piece where it
started, so a composite of idempotents stays a legitimate numerator at the same twist.

## The uniform family, and why peeling beats `⨁_F`

`signIdemAt γ i₀` instantiates the splitting at `Finsupp.erase`, so there is one idempotent per
*variable of `ι`* rather than one per splitting — which is what an induction over variables
needs. `signIdemAt_eq_self_of_apply_eq_zero` says it is the **identity** at any variable the
denominator does not invert.

That single fact is what makes the peeling route terminate. Splitting `C = e_{i₀}C ⊕ (1-e_{i₀})C`
and recursing on the second summand, `(1 - e_{i₀})` kills every term whose denominator omits
`i₀`, so after peeling `r` variables the complex vanishes in every degree below `r - 1` — a
Čech tuple of length `n+1` cannot contain `r > n+1` distinct variables. Each `Hⁿ` is therefore
settled by finitely many peels, with no bound needed on `ι` itself.

The `⨁_{F ⊆ supp γ}` decomposition would instead need `∑_F π_F = 1`, a powerset expansion of
`∏_j (e_j + (1 - e_j))` in `AddMonoidHom.End` — a **noncommutative** ring, so `Finset.prod_add`
does not apply — and it would need homology to commute with infinite products. Peeling needs
neither.

## What this file does not assert

Nothing here assembles `signIdemAt` into a chain map on the Čech complex, builds the block
subcomplexes, or says anything about `Hⁿ`. It supplies the commuting idempotent family, its
uniform indexing, and both halves of the face case analysis a chain-map proof consumes.

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

/-! ## The face that inserts the projected variable

`signProjection_laurentFace_comm` (#539) covers every Čech face `X_e` with `e ≠ i₀`; its
hypothesis `δ' i₀ = 0` unfolds to exactly that condition. The face `e = i₀` is **not** covered by
it — that statement forces `c = δ i₀ = γ i₀`, while inserting `X_{i₀}` makes `δ i₀ = γ i₀ + 1`,
so it cannot even be instantiated there. Nor is it the retraction
`signProjection_laurentFace`, which concerns the face from `γ'` into `γ`.

It is a third statement, and it holds for a clean reason: **a Čech face preserves the Laurent
exponent.** It multiplies numerator and denominator by the same `X_e^m`, so `α` is unchanged, and
`signIdem` is a condition on `α` alone. Both sides reduce to
`X_{i₀}^{m(c+1)} · (p /ᵐᵒⁿᵒᵐⁱᵃˡ X_{i₀}^{m·c})`.

With `signProjection_laurentFace_comm` this is the full case analysis a chain-map proof needs. -/

set_option maxHeartbeats 1600000 in
theorem signIdem_laurentFace_same [IsDomain R] {γ γ' δ : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0)
    (hδ : δ = Finsupp.single i₀ (c + 1) + γ')
    (hδγ : δ = Finsupp.single i₀ 1 + γ) (d : ℕ)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (natShift (polynomialGrading ι R) d)
      (.powers (MvPolynomial.monomial γ (1 : R)))) :
    signIdem hδ hγ' d (laurentFace hδγ d z) =
      laurentFace hδγ d (signIdem hγ hγ' d z) := by
  obtain ⟨m, p, hp, rfl⟩ :=
    DegreeZeroLocalization.exists_awayMk (monomial_one_mem_polynomialGrading (R := R) γ)
      (monomial_one_pow_ne_zero γ) z
  have hdegδ : δ.degree = 1 + γ.degree := by rw [hδγ, map_add, Finsupp.degree_single]
  have hmono1 : (MvPolynomial.monomial (Finsupp.single i₀ 1) (1 : R)) ^ m =
      MvPolynomial.monomial (Finsupp.single i₀ m) 1 := by
    rw [monomial_one_pow, Finsupp.smul_single, smul_eq_mul, Nat.mul_one]
  -- face of z, and its membership at δ
  have hface : (MvPolynomial.monomial (Finsupp.single i₀ 1) (1 : R)) ^ m • p ∈
      natShift (polynomialGrading ι R) d (m • (1 + γ.degree)) :=
    monomial_single_pow_smul_mem hp
  have hfaceδ : (MvPolynomial.monomial (Finsupp.single i₀ 1) (1 : R)) ^ m • p ∈
      natShift (polynomialGrading ι R) d (m • δ.degree) := by rw [hdegδ]; exact hface
  -- the two numerator identities
  have hsplit : Finsupp.single i₀ (m * (c + 1)) =
      Finsupp.single i₀ m + Finsupp.single i₀ (m * c) := by
    rw [← Finsupp.single_add]; congr 1; ring
  have hL : MvPolynomial.divMonomial
      ((MvPolynomial.monomial (Finsupp.single i₀ 1) (1 : R)) ^ m • p)
      (Finsupp.single i₀ (m * (c + 1))) =
      MvPolynomial.divMonomial p (Finsupp.single i₀ (m * c)) := by
    rw [hmono1, smul_eq_mul, hsplit, divMonomial_monomial_mul_add]
  have hR : MvPolynomial.monomial (Finsupp.single i₀ m) (1 : R) *
      (MvPolynomial.monomial (Finsupp.single i₀ (m * c)) 1 *
        MvPolynomial.divMonomial p (Finsupp.single i₀ (m * c))) =
      MvPolynomial.monomial (Finsupp.single i₀ (m * (c + 1))) 1 *
        MvPolynomial.divMonomial p (Finsupp.single i₀ (m * c)) := by
    rw [← mul_assoc, MvPolynomial.monomial_mul, one_mul, ← hsplit]
  rw [laurentFace_awayMk hδγ hp hface,
    DegreeZeroLocalization.awayMk_deg_congr hdegδ.symm (monomial_mem_add_degree hδγ)
      (monomial_one_mem_polynomialGrading (R := R) δ) m _ hface hfaceδ,
    signIdem_awayMk hδ hγ' hfaceδ (monomial_mul_divMonomial_mem hδ hfaceδ),
    signIdem_awayMk hγ hγ' hp (monomial_mul_divMonomial_mem hγ hp),
    laurentFace_awayMk hδγ (monomial_mul_divMonomial_mem hγ hp)
      (monomial_single_pow_smul_mem (monomial_mul_divMonomial_mem hγ hp)),
    DegreeZeroLocalization.awayMk_deg_congr hdegδ.symm (monomial_mem_add_degree hδγ)
      (monomial_one_mem_polynomialGrading (R := R) δ) m _
      (monomial_single_pow_smul_mem (monomial_mul_divMonomial_mem hγ hp))
      (by rw [hdegδ]; exact monomial_single_pow_smul_mem (monomial_mul_divMonomial_mem hγ hp))]
  have hcongr : ∀ (a b : MvPolynomial ι R)
      (ha : a ∈ natShift (polynomialGrading ι R) d (m • δ.degree))
      (hb : b ∈ natShift (polynomialGrading ι R) d (m • δ.degree)), a = b →
      DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
          (monomial_one_mem_polynomialGrading (R := R) δ) m a ha =
        DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
          (monomial_one_mem_polynomialGrading (R := R) δ) m b hb := by
    rintro a b ha hb rfl; rfl
  refine hcongr _ _ _ _ ?_
  rw [hL, hmono1, smul_eq_mul, hR]

/-! ## The uniform family -/

/-- Every exponent vector splits at a chosen variable. -/
theorem single_add_erase (γ : ι →₀ ℕ) (i₀ : ι) :
    γ = Finsupp.single i₀ (γ i₀) + γ.erase i₀ := by
  classical
  ext j
  by_cases hj : j = i₀
  · subst hj; simp [Finsupp.erase_same]
  · simp [Ne.symm hj, Finsupp.erase_ne hj]

/-- **The sign projection at a variable**, with the splitting supplied uniformly.

Indexed by a variable of `ι` rather than by a splitting, which is what an induction over
variables consumes. -/
noncomputable def signIdemAt [IsDomain R] (γ : ι →₀ ℕ) (i₀ : ι) (d : ℕ) :
    DegreeZeroLocalization (polynomialGrading ι R)
        (natShift (polynomialGrading ι R) d)
        (.powers (MvPolynomial.monomial γ (1 : R))) →+
      DegreeZeroLocalization (polynomialGrading ι R)
        (natShift (polynomialGrading ι R) d)
        (.powers (MvPolynomial.monomial γ (1 : R))) :=
  signIdem (single_add_erase γ i₀) Finsupp.erase_same d

set_option maxHeartbeats 1200000 in
/-- **At a variable the denominator does not invert, the projection is the identity.**

No Laurent monomial over `Xᵞ` can have a negative exponent at a variable `Xᵞ` does not invert,
so there is nothing for the truncation to remove: the divisor is `X_{i₀}^{m·0} = 1`.

This is what makes the peeling induction terminate. `1 - signIdemAt γ i₀` annihilates every term
whose denominator omits `i₀`, so peeling `r` distinct variables kills every Čech degree below
`r - 1`. -/
theorem signIdemAt_eq_self_of_apply_eq_zero [IsDomain R] {γ : ι →₀ ℕ} {i₀ : ι} (d : ℕ)
    (h0 : γ i₀ = 0)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (natShift (polynomialGrading ι R) d)
      (.powers (MvPolynomial.monomial γ (1 : R)))) :
    signIdemAt γ i₀ d z = z := by
  obtain ⟨m, p, hp, rfl⟩ :=
    DegreeZeroLocalization.exists_awayMk (monomial_one_mem_polynomialGrading (R := R) γ)
      (monomial_one_pow_ne_zero γ) z
  have hz : m * γ i₀ = 0 := by rw [h0, Nat.mul_zero]
  have hres : MvPolynomial.monomial (Finsupp.single i₀ (m * γ i₀)) (1 : R) *
      MvPolynomial.divMonomial p (Finsupp.single i₀ (m * γ i₀)) ∈
      natShift (polynomialGrading ι R) d (m • γ.degree) := by
    rw [hz, Finsupp.single_zero, MvPolynomial.divMonomial_zero,
      MvPolynomial.monomial_zero', map_one, one_mul]
    exact hp
  rw [signIdemAt, signIdem_awayMk _ _ hp hres]
  have hcongr : ∀ (a b : MvPolynomial ι R)
      (ha : a ∈ natShift (polynomialGrading ι R) d (m • γ.degree))
      (hb : b ∈ natShift (polynomialGrading ι R) d (m • γ.degree)), a = b →
      DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
          (monomial_one_mem_polynomialGrading (R := R) γ) m a ha =
        DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
          (monomial_one_mem_polynomialGrading (R := R) γ) m b hb := by
    rintro a b ha hb rfl; rfl
  exact hcongr _ _ _ hp (by
    rw [hz, Finsupp.single_zero, MvPolynomial.divMonomial_zero,
      MvPolynomial.monomial_zero', map_one, one_mul])

end AlgebraicGeometry.Proj
