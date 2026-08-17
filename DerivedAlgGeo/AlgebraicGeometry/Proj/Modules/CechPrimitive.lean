/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.CechHomotopy

/-!
# The primitive of a Čech cocycle of `O(d)`, `d ≥ 0`

The vanishing computation of #340, in cochain form. Given a degree-`(n+1)` cochain `s` of the
variable Čech cover whose differential vanishes, `cechPrimitive` is the cochain `t` with
`d t = s`: per block `F`, a cone point `i₀ ∉ F` is chosen and the block component of `s` is
contracted through the homotopy `y ↦ Π (s_F (i₀ :: y))`; the finitely many blocks of each
tuple then reassemble by `sum_cechBlockProj`.

* `cechBlockPrimitive` — the per-block candidate primitive. For a block with no cone point —
  only possible when the block is all of a finite variable set — it is `0`, and
  `cechBlockProj_eq_zero_of_forall_mem` says the block component of *everything* vanishes
  there: such a block would need every variable's exponent negative, while the twist `d ≥ 0`
  fixes the total at `d`. This is where nonnegativity of the twist is spent, and the only
  place.
* `cechPrimitive_isPrimitive` — **the homotopy computation** `d (h s) + h (d s) = s`,
  elementwise. The `j = 0` face of the cone tuple returns the block component through the
  retraction (`cechHomotopy_cechFace_zero`); every other face cancels between the two sides
  through the square (`cechHomotopy_cechFace_succ`); and the per-block identities sum over
  `(tupleExponent x).support.powerset` to `s x`.

The statement is against the face maps directly, not against the complex; the complex-level
exactness and the `Hⁿ(Pⁿ, O(d)) = 0` statement are derived downstream, where
`polynomialVariableCechComplex_d_apply` converts between the two forms.

## Tags

contracting homotopy, Čech cohomology, projective space, vanishing
-/

open MvPolynomial

namespace AlgebraicGeometry.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## The top block is empty for a nonnegative twist -/

variable {ι R : Type u} [CommRing R]

/-- If every variable lies in `F`, the block-`F` component of a legitimate numerator vanishes:
its Laurent exponents would be everywhere negative while their total is the twist `d ≥ 0`.
The witness `j₀` rules out the empty variable set, where the empty block carries the
constants. This is the only place the nonnegativity of the twist enters the vanishing
argument. -/
theorem laurentFilter_eq_zero_of_forall_mem (j₀ : ι) {F : Finset ι} (hF : ∀ j : ι, j ∈ F)
    {γ : ι →₀ ℕ} {d m : ℕ} {p : MvPolynomial ι R}
    (hp : p ∈ natShift (polynomialGrading ι R) d (m • γ.degree)) :
    laurentFilter γ m F p = 0 := by
  ext β
  rw [MvPolynomial.coeff_zero]
  by_cases hN : intNegSupport (laurentExponent γ m β) = F
  · rw [coeff_laurentFilter_of_eq hN]
    by_contra hc
    have hβs : β ∈ p.support := MvPolynomial.mem_support_iff.mpr hc
    have hdeg : (laurentExponent γ m β).degree = d :=
      degree_laurentExponent γ β m d (degree_eq_of_mem_support hp hβs)
    have hneg : ∀ j : ι, laurentExponent γ m β j < 0 := fun j =>
      mem_intNegSupport.mp (hN.symm ▸ hF j)
    have hj₀ : j₀ ∈ (laurentExponent γ m β).support :=
      Finsupp.mem_support_iff.mpr (by have := hneg j₀; omega)
    have hlt : (laurentExponent γ m β).degree < 0 := by
      rw [Finsupp.degree_apply]
      calc ∑ j ∈ (laurentExponent γ m β).support, laurentExponent γ m β j
          < ∑ _j ∈ (laurentExponent γ m β).support, (0 : ℤ) :=
            Finset.sum_lt_sum_of_nonempty ⟨j₀, hj₀⟩ fun j _ => hneg j
        _ = 0 := Finset.sum_const_zero
    omega
  · rw [coeff_laurentFilter_of_ne hN]

/-- The block of everything, over a nonempty variable set, projects everything to zero when
the twist is nonnegative. -/
theorem blockProj_eq_zero_of_forall_mem [IsDomain R] (j₀ : ι) {F : Finset ι}
    (hF : ∀ j : ι, j ∈ F) (γ : ι →₀ ℕ) (d : ℕ)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (natShift (polynomialGrading ι R) d) (.powers (MvPolynomial.monomial γ (1 : R)))) :
    blockProj (isPolynomialTwist_natShift (R := R) d) γ F z = 0 := by
  obtain ⟨m, p, hp, rfl⟩ := DegreeZeroLocalization.exists_awayMk
    (monomial_one_mem_polynomialGrading (R := R) γ) (monomial_one_pow_ne_zero γ) z
  rw [blockProj_awayMk (isPolynomialTwist_natShift (R := R) d) γ F]
  have hcongr : ∀ (a : MvPolynomial ι R)
      (ha : a ∈ natShift (polynomialGrading ι R) d (m • γ.degree)), a = 0 →
      DegreeZeroLocalization.awayMk (𝓜 := natShift (polynomialGrading ι R) d)
          (monomial_one_mem_polynomialGrading (R := R) γ) m a ha = 0 := by
    rintro a ha rfl
    exact DegreeZeroLocalization.awayMk_zero (monomial_one_mem_polynomialGrading (R := R) γ) m
  exact hcongr _ _ (laurentFilter_eq_zero_of_forall_mem j₀ hF hp)

variable (ι k : Type u) [Field k]

/-- The Čech form: any tuple supplies the witness. -/
theorem cechBlockProj_eq_zero_of_forall_mem (d : ℕ) {n : ℕ} (x : Fin (n + 1) → ι)
    {F : Finset ι} (hF : ∀ j : ι, j ∈ F) (z : polynomialVariableCechTerm ι k d n x) :
    cechBlockProj ι k d x F z = 0 := by
  rw [cechBlockProj_apply, blockProj_eq_zero_of_forall_mem (x 0) hF, map_zero]

/-! ## Support bookkeeping for the reassembly -/

/-- Dropping an index shrinks the support of the tuple exponent. -/
theorem tupleExponent_support_succAbove {n : ℕ} (x : Fin (n + 2) → ι) (j : Fin (n + 2)) :
    (tupleExponent ι (x ∘ j.succAbove)).support ⊆ (tupleExponent ι x).support := by
  intro a ha
  rw [Finsupp.mem_support_iff] at ha ⊢
  have happ := congrArg (fun v : ι →₀ ℕ => v a) (tupleExponent_succAbove x j)
  simp only [Finsupp.add_apply] at happ
  omega

/-- A block of the cone tuple avoiding the cone point is a block of the base tuple. -/
theorem subset_of_subset_cons {n : ℕ} {F : Finset ι} {i₀ : ι} (hi₀ : i₀ ∉ F)
    (y : Fin (n + 1) → ι)
    (h : F ⊆ (tupleExponent ι (Fin.cons i₀ y)).support) :
    F ⊆ (tupleExponent ι y).support := by
  intro a haF
  have ha := h haF
  rw [Finsupp.mem_support_iff] at ha ⊢
  have happ := congrArg (fun v : ι →₀ ℕ => v a) (tupleExponent_cons i₀ y)
  simp only [Finsupp.add_apply] at happ
  rcases eq_or_ne a i₀ with rfl | hne
  · exact absurd haF hi₀
  · rw [Finsupp.single_eq_of_ne hne] at happ
    omega

/-- The block projections commute with the inverse tuple transport. -/
theorem cechTermCongr_symm_cechBlockProj (d : ℕ) {n : ℕ} {x₁ x₂ : Fin (n + 1) → ι}
    (h : x₁ = x₂) (F : Finset ι) (z : polynomialVariableCechTerm ι k d n x₂) :
    (cechTermCongr ι k d h).symm (cechBlockProj ι k d x₂ F z) =
      cechBlockProj ι k d x₁ F ((cechTermCongr ι k d h).symm z) := by
  subst h; rfl

/-! ## The candidate primitive -/

open Classical in
/-- The per-block candidate primitive: contract the block-`F` component of `s` through the
cone point, when one exists. A block with no cone point contributes nothing — and by
`cechBlockProj_eq_zero_of_forall_mem` it has nothing to contribute. -/
noncomputable def cechBlockPrimitive (d : ℕ) {n : ℕ} (F : Finset ι)
    (s : ∀ x : Fin (n + 2) → ι, polynomialVariableCechTerm ι k d (n + 1) x)
    (y : Fin (n + 1) → ι) : polynomialVariableCechTerm ι k d n y :=
  if h : ∃ i₀, i₀ ∉ F then
    cechHomotopy ι k d h.choose y
      (cechBlockProj ι k d (Fin.cons h.choose y) F (s (Fin.cons h.choose y)))
  else 0

theorem cechBlockPrimitive_of_exists (d : ℕ) {n : ℕ} {F : Finset ι} (h : ∃ i₀, i₀ ∉ F)
    (s : ∀ x : Fin (n + 2) → ι, polynomialVariableCechTerm ι k d (n + 1) x)
    (y : Fin (n + 1) → ι) :
    cechBlockPrimitive ι k d F s y =
      cechHomotopy ι k d h.choose y
        (cechBlockProj ι k d (Fin.cons h.choose y) F (s (Fin.cons h.choose y))) := by
  rw [cechBlockPrimitive, dif_pos h]

theorem cechBlockPrimitive_of_forall (d : ℕ) {n : ℕ} {F : Finset ι} (h : ¬ ∃ i₀, i₀ ∉ F)
    (s : ∀ x : Fin (n + 2) → ι, polynomialVariableCechTerm ι k d (n + 1) x)
    (y : Fin (n + 1) → ι) :
    cechBlockPrimitive ι k d F s y = 0 := by
  rw [cechBlockPrimitive, dif_neg h]

/-- The per-block primitive of a block off the tuple's support vanishes: the cone point is
outside the block, so the cone tuple's support helps only through the base tuple's. -/
theorem cechBlockPrimitive_eq_zero_of_not_subset (d : ℕ) {n : ℕ} {F : Finset ι}
    (s : ∀ x : Fin (n + 2) → ι, polynomialVariableCechTerm ι k d (n + 1) x)
    {y : Fin (n + 1) → ι} (h : ¬ F ⊆ (tupleExponent ι y).support) :
    cechBlockPrimitive ι k d F s y = 0 := by
  by_cases hF : ∃ i₀, i₀ ∉ F
  · rw [cechBlockPrimitive_of_exists ι k d hF,
      cechBlockProj_eq_zero_of_not_subset ι k d _
        (fun hsub => h (subset_of_subset_cons (ι := ι) hF.choose_spec y hsub)), map_zero]
  · exact cechBlockPrimitive_of_forall ι k d hF s y

/-- The candidate primitive: the finitely many blocks of the tuple, contracted and summed. -/
noncomputable def cechPrimitive (d : ℕ) {n : ℕ}
    (s : ∀ x : Fin (n + 2) → ι, polynomialVariableCechTerm ι k d (n + 1) x)
    (y : Fin (n + 1) → ι) : polynomialVariableCechTerm ι k d n y :=
  ∑ F ∈ (tupleExponent ι y).support.powerset, cechBlockPrimitive ι k d F s y

/-! ## The homotopy computation -/

set_option maxHeartbeats 1600000 in
/-- **The per-block homotopy identity.** For each block `F` of the tuple `x`, the alternating
sum of the faces of the per-block primitive is the block-`F` component of `s x`.

With a cone point `i₀ ∉ F`: apply the block projection and the homotopy map to the cocycle
identity at `i₀ :: x`; the `j = 0` face returns `(s x)_F` through the retraction, and the
`j.succ` faces are exactly the faces of the per-block primitive, with one sign lost, through
the square. Without a cone point both sides vanish — the block of everything is empty for a
nonnegative twist. -/
theorem cechBlockPrimitive_faces (d : ℕ) {n : ℕ}
    (s : ∀ x : Fin (n + 2) → ι, polynomialVariableCechTerm ι k d (n + 1) x)
    (hs : ∀ x : Fin (n + 3) → ι,
      ∑ j : Fin (n + 3), (-1 : ℤ) ^ (j : ℕ) •
        polynomialVariableCechFace ι k d x j (s (x ∘ j.succAbove)) = 0)
    (x : Fin (n + 2) → ι) (F : Finset ι) :
    ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        polynomialVariableCechFace ι k d x j
          (cechBlockPrimitive ι k d F s (x ∘ j.succAbove)) =
      cechBlockProj ι k d x F (s x) := by
  by_cases hF : ∃ i₀, i₀ ∉ F
  · obtain hi₀ := hF.choose_spec
    have happlied := congrArg
      (fun z => cechHomotopy ι k d hF.choose x
        (cechBlockProj ι k d (Fin.cons hF.choose x) F z)) (hs (Fin.cons hF.choose x))
    simp only [map_sum, map_zsmul, map_zero] at happlied
    rw [Fin.sum_univ_succ] at happlied
    -- The `0`-face returns the block component through the retraction.
    have hterm0 : cechHomotopy ι k d hF.choose x
        (cechBlockProj ι k d (Fin.cons hF.choose x) F
          (polynomialVariableCechFace ι k d (Fin.cons hF.choose x) 0
            (s (Fin.cons hF.choose x ∘ (0 : Fin (n + 3)).succAbove)))) =
        cechBlockProj ι k d x F (s x) := by
      rw [← cechTermCongr_symm_apply_section ι k d s (cons_comp_succAbove_zero hF.choose x),
        ← cechFace_cechBlockProj, ← cechTermCongr_symm_cechBlockProj ι k,
        cechHomotopy_cechFace_zero ι k d hF.choose hi₀ x (s x)]
    -- Each `j.succ` face is a face of the per-block primitive, through the square.
    have htermsucc : ∀ j : Fin (n + 2), cechHomotopy ι k d hF.choose x
        (cechBlockProj ι k d (Fin.cons hF.choose x) F
          (polynomialVariableCechFace ι k d (Fin.cons hF.choose x) j.succ
            (s (Fin.cons hF.choose x ∘ (j.succ).succAbove)))) =
        polynomialVariableCechFace ι k d x j
          (cechBlockPrimitive ι k d F s (x ∘ j.succAbove)) := by
      intro j
      rw [← cechTermCongr_symm_apply_section ι k d s
          (cons_comp_succAbove_succ hF.choose x j),
        ← cechFace_cechBlockProj, ← cechTermCongr_symm_cechBlockProj ι k,
        cechHomotopy_cechFace_succ, cechBlockPrimitive_of_exists ι k d hF]
    rw [hterm0] at happlied
    have hsum : ∑ j : Fin (n + 2), (-1 : ℤ) ^ (((j.succ : Fin (n + 3))) : ℕ) •
        cechHomotopy ι k d hF.choose x
          (cechBlockProj ι k d (Fin.cons hF.choose x) F
            (polynomialVariableCechFace ι k d (Fin.cons hF.choose x) j.succ
              (s (Fin.cons hF.choose x ∘ (j.succ).succAbove)))) =
        -∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
          polynomialVariableCechFace ι k d x j
            (cechBlockPrimitive ι k d F s (x ∘ j.succAbove)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [htermsucc j, Fin.val_succ, pow_succ, mul_neg_one, neg_zsmul]
    rw [hsum] at happlied
    have h0 : ((0 : Fin (n + 3)) : ℕ) = 0 := rfl
    rw [h0, pow_zero, one_smul] at happlied
    exact (add_neg_eq_zero.mp happlied).symm
  · have hall : ∀ j : ι, j ∈ F := by
      intro j
      by_contra hj
      exact hF ⟨j, hj⟩
    rw [cechBlockProj_eq_zero_of_forall_mem ι k d x hall]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [cechBlockPrimitive_of_forall ι k d hF, map_zero]
    exact (AddMonoidHom.mk' (fun a : polynomialVariableCechTerm ι k d (n + 1) x =>
      ((-1 : ℤ) ^ (j : ℕ)) • a)
      fun a b => smul_add ((-1 : ℤ) ^ (j : ℕ)) a b).map_zero

set_option maxHeartbeats 1600000 in
/-- **The vanishing computation.** The alternating face sum of `cechPrimitive s` is `s`: per
block the previous identity applies — after extending each tuple's block sum to the blocks of
`x`, which costs nothing since a block off a tuple's support contributes zero — and the block
components of `s x` reassemble by `sum_cechBlockProj`. -/
theorem cechPrimitive_isPrimitive (d : ℕ) {n : ℕ}
    (s : ∀ x : Fin (n + 2) → ι, polynomialVariableCechTerm ι k d (n + 1) x)
    (hs : ∀ x : Fin (n + 3) → ι,
      ∑ j : Fin (n + 3), (-1 : ℤ) ^ (j : ℕ) •
        polynomialVariableCechFace ι k d x j (s (x ∘ j.succAbove)) = 0)
    (x : Fin (n + 2) → ι) :
    ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        polynomialVariableCechFace ι k d x j (cechPrimitive ι k d s (x ∘ j.succAbove)) =
      s x := by
  have hext : ∀ j : Fin (n + 2), cechPrimitive ι k d s (x ∘ j.succAbove) =
      ∑ F ∈ (tupleExponent ι x).support.powerset,
        cechBlockPrimitive ι k d F s (x ∘ j.succAbove) := by
    intro j
    rw [cechPrimitive]
    refine Finset.sum_subset ?_ fun F _ hFnot => ?_
    · intro F hFmem
      rw [Finset.mem_powerset] at hFmem ⊢
      exact hFmem.trans (tupleExponent_support_succAbove (ι := ι) x j)
    · exact cechBlockPrimitive_eq_zero_of_not_subset ι k d s
        fun hsub => hFnot (Finset.mem_powerset.mpr hsub)
  calc ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        polynomialVariableCechFace ι k d x j (cechPrimitive ι k d s (x ∘ j.succAbove))
      = ∑ j : Fin (n + 2), ∑ F ∈ (tupleExponent ι x).support.powerset,
          (-1 : ℤ) ^ (j : ℕ) • polynomialVariableCechFace ι k d x j
            (cechBlockPrimitive ι k d F s (x ∘ j.succAbove)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hext j, map_sum]
        exact map_sum ((AddMonoidHom.mk' (fun a => ((-1 : ℤ) ^ (j : ℕ)) • a)
          fun a b => smul_add ((-1 : ℤ) ^ (j : ℕ)) a b :
            polynomialVariableCechTerm ι k d (n + 1) x →+
              polynomialVariableCechTerm ι k d (n + 1) x)) _ _
    _ = ∑ F ∈ (tupleExponent ι x).support.powerset, ∑ j : Fin (n + 2),
          (-1 : ℤ) ^ (j : ℕ) • polynomialVariableCechFace ι k d x j
            (cechBlockPrimitive ι k d F s (x ∘ j.succAbove)) := Finset.sum_comm
    _ = ∑ F ∈ (tupleExponent ι x).support.powerset, cechBlockProj ι k d x F (s x) :=
        Finset.sum_congr rfl fun F _ => cechBlockPrimitive_faces ι k d s hs x F
    _ = s x := sum_cechBlockProj ι k d x (s x)

end AlgebraicGeometry.Proj
