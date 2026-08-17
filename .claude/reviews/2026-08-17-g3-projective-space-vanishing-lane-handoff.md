# G3 lane — `Hⁱ(Pⁿ, O(d))` vanishing: review and continuation handoff

**Audience:** a working session (autonomous or interactive) picking up #340 / #491.
Not a human summary.
**Baseline:** `origin/main` at `844a4ae` (merge of PR #526). Everything below assumes
that commit. Ratchet ceilings at this baseline: AlgebraicGeometry **1098**,
StabilityCondition **380**, DGCategory **0**
(`scripts/check_audit_complete.py:CEILINGS`).
**Issues:** #340 (`G3: Hⁱ(Pⁿ, O(d)) = 0 for i > 0 and d ≥ 0, from the explicit Čech
complex`, label `blocked`) and #491 (`G3a: Laurent monomial basis and the sign
projection`, labels `ready` / `agent-ready`).
**Read first:** the two comments on #340 —
[the scoping resolution](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/340#issuecomment-5295798851)
and [the proof plan](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/340#issuecomment-5309409750).
The second **corrects** the first on the shape of the proof; the correction is the
reason this lane looks the way it does.

## 0. How to work (non-negotiable mechanics)

```bash
cd /Users/chris.dare/Personal/SourceCode/derived-alg-geo-lean
git fetch origin
git worktree add -b agent/<your-branch> /tmp/<your-dir> origin/main
mkdir -p /tmp/<your-dir>/.lake
ln -sfn /Users/chris.dare/Personal/SourceCode/derived-alg-geo-lean/.lake/packages \
        /tmp/<your-dir>/.lake/packages
cp -Rc /Users/chris.dare/Personal/SourceCode/derived-alg-geo-lean/.lake/build \
       /tmp/<your-dir>/.lake/build      # APFS clone, ~20s; avoids a Mathlib rebuild
cp -Rc /Users/chris.dare/Personal/SourceCode/derived-alg-geo-lean/.lake/config \
       /tmp/<your-dir>/.lake/config
cd /tmp/<your-dir> && lake build && scripts/gates.sh
```

- **Never work in the shared checkout.** It switches branches mid-run.
- Gates are the definition of done: `scripts/gates.sh` must print
  `all gates passed (full)` — 17 gates, ~5 min warm.
- **Every new public declaration goes in `scripts/AlgebraicGeometryAudit.lean`.**
  The ceiling is exact; one unaudited decl fails `audit-complete`. Two traps this
  lane already hit:
  - **Auto-generated declarations count.** `awayMk` carries its membership
    certificate as a dependent argument, so the first `rw [coe_awayMk]` in a file
    makes Lean emit `awayMk.congr_simp`. A `structure` emits `mk.inj`,
    `mk.sizeOf_spec`, and every field projection. `AwayRep` cost six audit lines
    on top of its theorems. Register them; do not let them widen the gap.
  - **A failed `assert` in an edit script silently writes nothing.** A batch edit
    to the audit file aborted before its single `write()` and 21 declarations went
    unregistered; only `audit-complete` caught it. Verify with
    `grep -c '<new-name>' scripts/AlgebraicGeometryAudit.lean` after editing.
- **The audit file is a single append-point and conflicts structurally** with every
  concurrent PR. Four of this lane's seven PRs conflicted there. Resolution is
  always "keep both blocks"; never take one side.
- `grep -c` exits **1** when the count is 0, which short-circuits a `&&` chain and
  can skip a `git commit`. Do not chain a verification `grep -c` before a commit.

### Merge mechanics (this cost more wall-clock than the mathematics)

- Branch protection **enforces up-to-date heads**. `main` moves every 10–20 minutes
  from other lanes, so a PR is `BEHIND` again within one CI cycle.
- Working pattern: arm `gh pr merge <n> --merge --auto` immediately after pushing,
  then bring the branch up to date. Auto-merge fires the moment the head is current
  and CI is green, which is the only way this repo's PRs land without babysitting.
- Re-run `scripts/gates.sh` locally only when `main`'s drift **touches your files**.
  When it does not (check `git diff --name-only HEAD origin/main`), `gh pr
  update-branch` is the right tool and skips a 5-minute build.
- **`gh pr view --json statusCheckRollup` is stale for seconds after a push.** It
  will report the *previous* head's checks as `SUCCESS`. Always compare
  `.headRefOid` against what you pushed before believing a green rollup. This
  nearly merged #499 on the wrong commit's checks.

## 1. What the mathematics is

`Hⁱ(Pⁿ, O(d)) = 0` for `i > 0`, `d ≥ 0`, where `Pⁿ = Proj (MvPolynomial ι k)` and
`ι` is **arbitrary** (possibly infinite).

The first comment on #340 said the proof needs a `ℤ^ι` grading on
`Localization (.powers g)` plus reduced simplicial cohomology of a simplex. **The
simplicial half is avoidable.** The route this lane implements:

1. **Decompose by Laurent multidegree.** Write `T x = Set.range x`, and for
   `α : ι →₀ ℤ` with `Σ α = d` write `N α = {j | α j < 0}` (finite). Then
   `(A(d)_{gₓ})₀ ≅ ⨁ {α | Σ α = d, N α ⊆ T x} k` — a Laurent monomial basis,
   negative exponents exactly on the inverted variables.

2. **Pull the sum out of the product.** `T x` is finite, so `N α ⊆ T x` ranges over
   finitely many `F` for each fixed `x`, hence
   ```
   Cⁿ = ∏ₓ (A(d)_{gₓ})₀  ≅  ∏_{F : Finset ι} C_F ⁿ,   C_F ⁿ = ∏ₓ ⨁ {α | N α = F} k
   ```
   and the Čech differential preserves `α`, hence `F`. **This is the step that keeps
   an infinite `ι` harmless** — an infinite product is never exchanged with an
   infinite direct sum. Homology commutes with products in `AddCommGrpCat`, so
   `Hⁿ(C) = ∏_F Hⁿ(C_F)`.

3. **Contract each block.** Fix `F`, pick `i₀ ∈ ι \ F`, and set
   `(h s) y = π (s (Fin.cons i₀ y))` where `π` keeps the monomials whose negative
   support still fits in `T y`. Then `d ∘ h + h ∘ d = id` on `C_F ⁿ` for `n ≥ 1`:
   the `j = 0` face of `Fin.cons i₀ y` returns `s y`, and the faces `j ≥ 1` cancel
   against `d (h s)` term by term, using `i₀ ∉ F` to know the extension-by-zero
   agrees on both sides. So `Hⁿ(C_F) = 0` for `n ≥ 1`.

4. **`d ≥ 0` finishes it.** `C_ι` is the only block without a cone point, and for
   `ι` finite it is *empty* when `d ≥ 0`: `N α = ι` forces `Σ α ≤ -|ι| < 0 ≠ d`. For
   `ι` infinite `N α` is finite, hence always proper. So every surviving `F` has a
   cone point.

**Do not use a single global `i₀`.** The cone point must lie outside `F = N α`, and
`F` varies with `α`. An earlier draft of this argument used one `i₀` for the whole
complex and is wrong; the per-block choice in step 2–3 is what makes it work.

Sanity check on `P¹`: `F = ∅` contributes `k^{d+1}` in degree 0; `F = {0}` and
`F = {1}` are killed by the homotopy; `F = {0,1}` is empty for `d ≥ 0` and has
dimension `-d-1` for `d ≤ -2`, which is the classical `h¹(P¹, O(d))`. The same
bookkeeping gives the negative-twist top group, so this lemma also covers the #332
dévissage input at `intShift` with no new idea.

## 2. What is landed

Seven PRs, all merged, all gated at 17/17, no `sorryAx`, no new axiom.

**#495** — `Cohomology/Finiteness/ProjectiveSpace.lean`.
`polynomialVariableCechComplex_computesCohomology`: for every `n : ℕ` and `d : ℕ`,
```
Nonempty (((polynomialVariableCechComplex ι k d).homology n : AddCommGrpCat.{u}) ≃+ (O(d)).H n)
```
Three lines of glue over #338 (`polynomialVariable_isCechAcyclicCover`), #331/#334
(`isCechAcyclicCover_cechComputesDerivedCohomologyAt_opens`) and #339
(`polynomialVariableCechComplexIso`). This is the statement #340 opens with and it
was **not** in `main` before. `HasExt.{u + 1}` is passed positionally throughout —
`Sheaf.H` lands in the `HasExt` universe, so `HasExt.{u}` and `HasExt.{u + 1}` name
different groups and instance search must not be allowed to pick.

**#496** — `Proj/Modules/GradedLocalization.lean`, the away-localization normal form.
- `exists_awayMk` — every degree-zero fraction away from `f` *is* `m / fⁿ`. The
  content is that the `NumDenSameDeg` degree certificate is pinned to `n • deg f`
  (`DirectSum.degree_eq_of_mem_mem`) once `fⁿ ≠ 0`. Hypothesis is `∀ n, fⁿ ≠ 0`, so
  no domain assumption; it cannot be dropped (a nilpotent `f` leaves the degree
  unconstrained).
- `awayMk_eq_awayMk_iff` — `p / fⁿ = q / fᵐ ↔ fᵐ • p = fⁿ • q`, no residual `∃ u`.
  **This is the only place `IsDomain A` and `Module.IsTorsionFree A M` are spent.**
  For `M = A` the latter is already an instance. Without torsion-freeness the
  statement is false, not merely unproved.
- `awayMk_zero`, `awayMk_add`, `awayMk_sum`, `awayMk_shift` — numerator additivity
  at a fixed denominator, plus the common-denominator move. All hold over an
  arbitrary ring.

**#499** — `Proj/Modules/LaurentBasis.lean`, the exponent.
`laurentExponent γ m β = β - m • γ : ι →₀ ℤ`, with
`awayMk_monomial_eq_iff_laurentExponent` making it a **complete invariant**,
`degree_laurentExponent` (total degree is the twist `d`, independent of `m` — this
is where `m` disappears) and `laurentExponent_nonneg_of_apply_eq_zero` (nonnegative
off `supp γ`). Together these index the monomial fractions of twist `d` by
`{α | α.degree = d ∧ ∀ j, γ j = 0 → 0 ≤ α j}`.

**#506** — spanning. `exists_sum_awayMk_monomial`: every fraction is a finite sum of
monomial fractions **over one common denominator**. `laurentExponent_mem_index` says
the exponents contributed are exactly the admissible ones. Note `awayMk_shift` is
*not* used here — splitting a numerator never touches `m`.

**#509** — independence. `sum_awayMk_monomial_eq_zero_iff` via the new
`awayMk_eq_zero_iff` (a fraction is zero exactly when its numerator is), reducing to
monomial independence in `MvPolynomial`. With #506 this is **step 1 of §1 in usable
form**: a map may be *defined* by its effect on monomial fractions.

**#511** — `Proj/Modules/LaurentProjection.lean`, numerator side of `π`.
`π` needs **no new construction**: on a representative `p / (Xᵞ)ᵐ` it is
`MvPolynomial.divMonomial`. Two load-bearing statements:
- `divMonomial_pow_mul` — the well-definedness identity
  `((Xᵞ)ᵗ · p) /ᵐᵒⁿᵒᵐⁱᵃˡ X_{i₀}^{(m+t)c} = (Xᵞ')ᵗ · (p /ᵐᵒⁿᵒᵐⁱᵃˡ X_{i₀}^{m·c})`.
- `divMonomial_mem_natShift` — only the denominator's contribution moves; the twist
  `d` is untouched, so `π` is a map of `O(d)`-sections.
- `divMonomial_monomial_mul_comm` requires **disjoint support**, and that is
  essential rather than technical: dividing `X_{i₀}` out of `X_{i₀} · p` is not
  `X_{i₀} ·` anything. It holds structurally because the factor pulled out is a
  power of `Xᵞ'`, which does not involve `i₀`.

**#526** — the descent and the retraction.
- `signProjection` — `π` as a map on the localization, via `AwayRep` +
  `Exists.choose`, pinned by `signProjection_awayMk`. **Callers should use the
  equation, never the definition.**
- `AwayRep.frac_project_congr` — well-definedness, and it is exactly the three facts
  above: `awayMk_eq_awayMk_iff` turns "same element" into a cross-multiplication;
  `frac_project_raise` (`divMonomial_pow_mul` on the numerator, `awayMk_shift` on
  the fraction) moves both projections to the common exponent `r₁.pow + r₂.pow`;
  there the cross-multiplication *is* equality of numerators.
- `signProjection_laurentFace` — **`π ∘ ι = id`**. `laurentFace` is
  `DegreeZeroLocalization.faceMap` at `g₁ · h = g₂` with `h = X_{i₀}^c`, i.e. the
  Čech face of #340's complex.
- New in `GradedLocalization.lean`: `faceMap_awayMk` (the face map in `awayMk`
  normal form — the shape every caller has) and `awayMk_deg_congr` (transport
  between two names for one degree; `awayMk` cannot see through it because the
  degree sits in its certificate).

`γ' i₀ = 0` is required by `signProjection`'s **equations**, not by its definition —
the definition is total either way; only independence of the choice needs it.

## 3. Review notes on what is landed

Things a reviewer should look at, or a continuation should not undo:

1. **`signProjection` is choice-based.** It is defined through `Exists.choose` on
   `AwayRep.frac_surjective`. That is deliberate — `DegreeZeroLocalization` is a
   submodule of `LocalizedModule`, not a quotient, so there is no `lift` to use. The
   consequence is that `signProjection` has no useful `rfl` behaviour; everything
   must go through `signProjection_awayMk`. If a continuation finds itself unfolding
   the definition, that is a sign the needed equation is missing, not that the
   definition is wrong.

2. **`signProjection` is not yet known to be additive.** It is a bare function, not
   an `AddMonoidHom`. The homotopy needs additivity. This is listed as work in §4
   and is the most likely place to be surprised: it requires putting two elements
   over a *common* denominator, which is the first genuine use of `awayMk_shift`
   outside `frac_project_raise`.

3. **The `γ = X_{i₀}^c · γ'` splitting is a hypothesis, not `Finsupp.erase`.** The
   caller is a Čech face, which produces the pieces separately (`c = 1`, `γ'` the
   denominator of the smaller intersection). Do not "simplify" this to `erase` — it
   would force every call site to prove the splitting it already has.

4. **`degree_eq_weight_one_apply` is a bridge, not a result.**
   `MvPolynomial.IsHomogeneous` unfolds to `Finsupp.weight 1` while its public API
   is stated with `Finsupp.degree`; the two are equal but not definitionally so, and
   `show`/`simp only` both fail to cross the gap. Keep it.

5. **Dependent-argument rewrites fail repeatedly in this lane.** `awayMk`'s
   membership proof mentions the numerator and the exponent, so `rw` on either
   produces a non-type-correct motive. Three separate proofs use the same
   workaround: a local `hcongr`/`hgen` that takes the equalities and discharges by
   `rintro ... rfl; rfl` (proof irrelevance). `awayMk_sum` instead descends into
   `LocalizedModule` first. Both are fine; reach for one of them rather than
   fighting `rw`.

6. **No statement in this lane asserts anything about `Hⁱ` yet** beyond #495. In
   particular nothing here proves vanishing, finite-dimensionality, or the top
   group. #340's acceptance criteria are all still open.

## 4. Continuation, in order

### Step 1 — the `faceMap` square (finishes #491)

The last property the homotopy consumes. For a tuple `x`, a face index `j`, and
`i₀ ∈ ι`:
```
π_{i₀::x → x} ∘ faceMap_{i₀::(x∘δⱼ) → i₀::x}
  = faceMap_{x∘δⱼ → x} ∘ π_{i₀::(x∘δⱼ) → x∘δⱼ}
```
**restricted to the summands with `i₀ ∉ N α`.** The restriction is essential — the
square does **not** commute unrestricted. Concretely it fails when `i₀ ∈ T x` but
`i₀ ∉ T (x ∘ δⱼ)` (i.e. `x j = i₀` and `i₀` occurs nowhere else): then the left side
keeps everything and the right side still requires `α i₀ ≥ 0`. This is exactly the
`i₀ ∉ F` hypothesis of §1 step 3, and it is why the homotopy is built per-block.

Inputs available: `laurentFace_awayMk`, `signProjection_awayMk`,
`divMonomial_monomial_mul_comm` (the disjointness hypothesis is what encodes the
restriction), `awayMk_deg_congr`.

Also needed here, and not yet proved:
- `signProjection` is additive (see §3.2) — promote it to `→+`.
- A common-denominator lemma for two elements: given `z₁, z₂`, representatives at a
  single shared `m`. This is `awayMk_shift` twice plus `exists_awayMk`.

### Step 2 — the block decomposition (`∏_F C_F`)

`Cⁿ ≅ ∏_{F : Finset ι} C_F ⁿ` **as cochain complexes**, not merely degreewise, and
`Hⁿ(C) = ∏_F Hⁿ(C_F)`.

The per-`x` finiteness of `{F | F ⊆ T x}` is what makes the map an isomorphism;
#506 + #509 give the basis it is stated against. `polynomialVariableCechComplex_d_apply`
is the differential to check preserves each block. Expect this to be the largest
single step — it is where the complex-level bookkeeping lives.

### Step 3 — the homotopy and vanishing

`d ∘ h + h ∘ d = id` on `C_F ⁿ` for `n ≥ 1`, with `h` built from `signProjection` and
`Fin.cons i₀`; then `Hⁿ(C_F) = 0`, then `C_ι = 0` for `d ≥ 0`, then
`Hⁿ(Pⁿ, O(d)) = 0` for `n ≥ 1` through #495.

### Step 4 — close out #340

- `H⁰` **must reuse** `polynomialTwistingGlobalSectionsModuleIso`
  (`Proj/Modules/ProjectiveSpace.lean`, `[Nontrivial ι]`), not be reproved. Note the
  `Nontrivial ι` hypothesis: `|ι| ≥ 2`. For `|ι| = 1` `Proj` is a point and for
  `ι` empty it is empty; state accordingly.
- `Module.Finite k (Hⁱ(Pⁿ, O(d)))` for every `i`, `d`, **with no finiteness
  hypothesis** — a corollary of steps 3 + 4, not an independent target. The first
  comment on #340 establishes why: every Čech cochain group is infinite-dimensional
  over `k`, so finiteness is never inherited from the terms.
- Retitle/relabel #340 off `blocked` and close #491.

### Not in scope

No dévissage to general coherent sheaves, no closed-immersion pushforward, no
`FiniteDimensionalCohomology` assembly — those stay on #332. No `ℤ^ι` graded-algebra
structure on the localization; the basis and the projection are what the consumer
needs and a full grading is strictly more work.

## 5. Estimate

Step 1 is one focused session. Step 2 is the risk — the product-of-blocks iso at
complex level, plausibly 300–600 lines. Steps 3–4 are short *given* step 2. Whole
remainder: roughly one to two weeks of focused Lean, not the "multi-week `ℤ^ι`
grading development" the first #340 comment implied.
