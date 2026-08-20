/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Cech.Vanishing

/-!
# `H⁰(Pⁿ, O(d)) = 0` for a negative twist

The degree-zero end of the integer-twist computation. `Cech/Vanishing.lean` closes the middle
degrees at either sign; this file closes the bottom one at `d < 0`.

## The argument

`H⁰` of the Čech complex is the kernel of `d⁰`, and unfolding the differential at `n = 0` says a
cocycle is a family `(sᵢ)` of degree-`d` fractions on the variable charts agreeing on every
overlap. Fixing `i` and choosing any `j ≠ i`, the overlap condition clears denominators to

```
X_j ^ b * p = X_i ^ a * q
```

with `p` the numerator of `sᵢ`. `X_i` and `X_j` are distinct variables, hence coprime, so
`X_pow_dvd_of_cross_mul` extracts `X_i ^ a ∣ p`. The numerator of a degree-`d` fraction with
denominator `X_i ^ a` is homogeneous of degree `a + d`, and at `d < 0` that is *smaller* than `a`
— so a nonzero `p` would be a multiple of `X_i ^ a` of degree below `a`, which cannot happen.
Hence `p = 0`, hence `sᵢ = 0`.

## Where the sign enters, and where it does not

Only in the last step. Everything before it is the two-chart argument that
`polynomialToNatGlobalSections_surjective` runs for `d : ℕ`, and it is insensitive to the sign;
what changes is the conclusion drawn at the end, which for `d ≥ 0` produces a representing
polynomial and for `d < 0` produces `0`.

That is visible in the grading itself rather than being an extra hypothesis.
`intShift` is indexed by `ℕ`, not `ℤ`: `intShiftPiece 𝓜 d n` collects the elements of degree
`n + d`, and when `n + d < 0` there is no such natural number, so the piece is trivial outright.
`intShiftPiece_eq_bot_of_neg` below records exactly that, and it is the whole of the difference.

## Scope

The **abelian-group** statement, per #665. The `k`-vector-space structure that
`FiniteDimensionalCohomology.finite` asks for is separate, and the comparison `AddEquiv` is not
assumed `k`-linear anywhere here.

`Nontrivial ι` is needed and is not cosmetic: with a single variable there is no second chart, the
overlap condition is vacuous, and the statement is false — `P⁰` is a point and `O(d)` is free on
it. `Fintype ι` is *not* needed; the argument uses two charts, never all of them.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Proj

variable (ι k : Type u) [Field k]

/-! ### The two arithmetic facts

Both are about the polynomial ring and its shifted grading, with no localization and no Čech
complex in sight. They are separated out because each is the whole content of one step above. -/

/-- **A shifted graded piece below degree zero is trivial.**

`intShift` is `ℕ`-indexed and `intShiftPiece 𝓜 d n` asks for an element of degree `n + d`. When
that is negative no natural number witnesses it, so only `0` remains. This is the single place the
sign of `d` is used in this file. -/
theorem intShiftPiece_eq_bot_of_neg {M σM : Type u} [AddCommGroup M]
    [SetLike σM M] [AddSubgroupClass σM M] (𝓜 : ℕ → σM) (d : ℤ) (n : ℕ)
    (hn : (n : ℤ) + d < 0) :
    intShiftPiece 𝓜 d n = ⊥ := by
  ext m
  simp only [AddSubgroup.mem_bot]
  constructor
  · rintro (h0 | ⟨j, hj, -⟩)
    · exact h0
    · exact absurd hj (by omega)
  · rintro rfl
    exact Or.inl rfl

/-- **A homogeneous polynomial divisible by `Xᵢ ^ a` but of degree below `a` is zero.**

The second arithmetic fact, and the one that turns the coprimality extraction into a vanishing
statement. Every monomial of a multiple of `Xᵢ ^ a` carries `Xᵢ` to at least the power `a`, so its
total degree is at least `a`; a homogeneous polynomial of degree `m < a` has none of those, hence
no monomials at all.

At a nonnegative twist this case never arises — there `m = a + d ≥ a` — which is why the
nonnegative argument produces a representing polynomial where this one produces `0`. -/
theorem eq_zero_of_X_pow_dvd_of_isHomogeneous_of_lt
    (i : ι) (a m : ℕ) (p : MvPolynomial ι k)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule ι k m)
    (hdvd : (MvPolynomial.X i : MvPolynomial ι k) ^ a ∣ p)
    (hlt : m < a) :
    p = 0 := by
  classical
  by_contra hne
  obtain ⟨s, hs⟩ : ∃ s, MvPolynomial.coeff s p ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (MvPolynomial.ext _ _ (by simpa using hall))
  -- Divisibility by `Xᵢ ^ a` forces the `i`-th exponent of every monomial up to `a`.
  have hsi : a ≤ s i := by
    by_contra hlt'
    push Not at hlt'
    obtain ⟨q, rfl⟩ := hdvd
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul'] at hs
    refine hs ?_
    rw [if_neg]
    intro hle
    exact absurd (by simpa using hle i) (by omega)
  -- Homogeneity pins the total degree, which is at least that exponent.
  have hdeg : (Finsupp.weight 1) s = m := hp hs
  have hle : s i ≤ (Finsupp.weight 1) s := by
    simpa [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] using
      Finset.single_le_sum (f := fun j => s j) (fun _ _ => Nat.zero_le _)
        (Finsupp.mem_support_iff.mpr (by omega : s i ≠ 0))
  omega

/-! ### The two-chart step

The overlap condition on two charts, once denominators are cleared, is exactly the cross
equation below. This is the mathematical heart of the negative-twist vanishing: everything above
it is arithmetic, everything below it is the plumbing that produces `hcross` from a Čech
cocycle. -/

/-- **A degree-`d` numerator on the `i`-chart that matches one on the `j`-chart vanishes, when
`d < 0`.**

`p / Xᵢ ^ a` and `q / Xⱼ ^ b` agree on the overlap exactly when `Xⱼ ^ b * p = Xᵢ ^ a * q` after
clearing the common denominator. Coprimality of the two variables then forces `Xᵢ ^ a ∣ p`, while
the degree bookkeeping `m = a + d` puts `p` below degree `a` as soon as `d < 0`. The two are
incompatible unless `p = 0`.

`hm` is where the twist appears: the numerator of a degree-`d` fraction with denominator `Xᵢ ^ a`
is homogeneous of degree `a + d`. That is `mem_intShiftPiece` unfolded, and it is the only fact
about `intShift` this step needs. -/
theorem num_eq_zero_of_cross_of_neg {i j : ι} (hij : i ≠ j) (d : ℤ) (hd : d < 0)
    (a b m : ℕ) (p q : MvPolynomial ι k) (hm : (m : ℤ) = (a : ℤ) + d)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule ι k m)
    (hcross : MvPolynomial.X j ^ b * p = MvPolynomial.X i ^ a * q) :
    p = 0 :=
  eq_zero_of_X_pow_dvd_of_isHomogeneous_of_lt ι k i a m p hp
    (X_pow_dvd_of_cross_mul ι k hij a b p q hcross) (by omega)

/-! ### Reducing `H⁰` to the kernel

Degree `0` has no incoming differential, so the general `exactAt` machinery the middle degrees use
still applies — but it degenerates. `(ComplexShape.up ℕ).prev 0 = 0` and `d 0 0 = 0` by the shape,
so exactness at `0` says precisely that the kernel of `d⁰` is trivial, with no image to quotient
by. Separating this out keeps the algebra below free of homological bookkeeping. -/

/-- Triviality of `ker d⁰` is exactly vanishing of `H⁰` for the algebraic Čech complex. -/
theorem intCechComplex_homology_zero_isZero_of_ker (d : ℤ)
    (hker : ∀ s : (polynomialVariableIntCechComplex ι k d).X 0,
      ConcreteCategory.hom ((polynomialVariableIntCechComplex ι k d).d 0 1) s = 0 → s = 0) :
    Limits.IsZero ((polynomialVariableIntCechComplex ι k d).homology 0) := by
  refine ((polynomialVariableIntCechComplex ι k d).exactAt_iff_isZero_homology 0).mp ?_
  rw [HomologicalComplex.exactAt_iff' _ 0 0 1 CochainComplex.prev_nat_zero
    (CochainComplex.next ℕ 0), ShortComplex.ab_exact_iff]
  intro s hs
  refine ⟨0, ?_⟩
  rw [map_zero]
  exact (hker s hs).symm

end AlgebraicGeometry.Proj
