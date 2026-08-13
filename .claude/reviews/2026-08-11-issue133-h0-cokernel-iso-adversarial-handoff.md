# Issue #133 adversarial handoff — H⁰′ cokernel comparison isomorphism

Date: 2026-08-11

Review target: the exact head of branch
`agent/issue-133-h0-cokernel-iso`. This branch is intentionally based on the
locally completed issue #90 commit; review the PR base and exact SHA when it is
published.

## Requested verdict

Return `SHIP`, `SHIP WITH FIXES`, or `DO NOT SHIP`. Separate theorem-soundness
findings from source/governance observations; this result carries no paper
citation or source-faithfulness claim.

## New public theorem

```lean
CategoryTheory.Triangulated.HeartStabilityData.
  isIso_heartSourceH0primeShortComplex_cokernelDesc_unconditional
```

For a distinguished triangle

```text
A ⟶ X₂ ⟶ X₃ ⟶ A[1]
```

with `A` in the heart, the theorem proves `IsIso` for the canonical map

```text
coker(A ⟶ H⁰′(X₂)) ⟶ H⁰′(X₃).
```

## Proof route

1. Install the already-proved local homological structure for `H0primeFunctor`.
2. Rotate the distinguished triangle to
   `X₂ ⟶ X₃ ⟶ A[1] ⟶ X₂[1]`.
3. Obtain exactness of its `H⁰′` image from
   `Functor.map_distinguished_exact`.
4. Use the heart condition `A ∈ D^{≤0}`, `TStructure.isLE_shift`, and
   `TStructure.isZero_truncGE_obj_of_isLE` to prove `H⁰′(A[1])` is zero.
5. Apply `ShortComplex.Exact.epi_f` to get `Epi (H⁰′g)`.
6. Rewrite through
   `heartSourceH0primeShortComplex_cokernelπ_comp_cokernelDesc` and use
   `epi_of_epi` to make the canonical comparison epic.
7. Reuse
   `mono_heartSourceH0primeShortComplex_cokernelDesc_unconditional` and finish
   with `isIso_of_mono_of_epi`.

## Boundaries to attack

- Confirm the rotation has the expected first two maps; a definitional
  coincidence in the wrong slot would invalidate the epicity step.
- Confirm the `H⁰′(A[1])` zero proof uses the correct sign convention:
  `A[1] ∈ D^{≤-1}`, hence `τ≥0(A[1]) = 0`.
- Confirm the epicity rewrite targets the same proof argument `hfg` as the
  canonical cokernel descriptor; check that proof irrelevance is not masking a
  different morphism.
- Confirm the existing monicity theorem has exactly the same hypotheses and
  morphism.
- Search for any accidental global homological instance. The theorem should
  use only local `letI` bindings.
- Reject any documentation that calls the original three-term complex
  `ShortExact`: the first map need not be monic because `H⁻¹(X₃)` can be
  nonzero.
- Confirm issue #89's seven public declarations and their statements are
  unchanged.

## Expected mechanical evidence after issues #90 and #133

- audit: 1,355 declarations, permitted axioms only, no `sorryAx`;
- census: 1,623 authored; 114 private; 154 structure projections; zero
  authored public declarations outside the audit;
- gated split: 945 theorems, 40 structures, 370 other non-theorems;
- coverage map unchanged at `{mapped: 2, target: 8}`;
- build, environment linter, emitter, registry validator, and
  `git diff --check` all pass.

The review must cite the exact commit SHA. It should not infer a mass theorem,
paper-level statement, `ShortExact` package, or human source review from this
categorical strengthening.
