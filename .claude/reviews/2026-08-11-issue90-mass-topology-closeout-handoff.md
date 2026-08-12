# Issue #90 adversarial handoff — mass/topology closeout

Date: 2026-08-11

Review target: branch `agent/issue-90-closeout` (review the exact PR head, not this
branch name alone).

## Requested verdict

Please return one of `SHIP`, `SHIP WITH FIXES`, or `DO NOT SHIP`, with separate
findings for Lean soundness, topology-instance safety, source faithfulness, and
registry governance. A green build is evidence only for the first of those.

## Delta

The long mass proof was already on current `main` through PR #135. This branch
does not port or duplicate it. It adds the single public corollary

```lean
CategoryTheory.Triangulated.stabilityDistanceTopologyCompatible
```

in
`BridgelandStabLean/StabilityCondition/Metric/Mass/Subadditivity/Triangle.lean`.
The proof applies
`stabilityDistanceTopologyCompatible_of_mass_triangle` to the existing
`stabilityMassTriangleInequality`.

It also:

- adds the theorem to `scripts/Audit.lean`;
- corrects stale comments in `Metric/Distance/Topology.lean`;
- corrects `formalization.yaml` and the statement registry so they no longer
  describe the mass theorem as absent;
- introduces the registry label `source-review-pending` and fixes the
  documented `mfc` CLI example to pass labels as separate arguments.

## Claims deliberately not made

- No `PseudoEMetricSpace`, `EMetricSpace`, topology, uniformity, or metric
  instance is installed.
- No existing conditional constructor is removed.
- Every citation to Bridgeland Proposition 8.1 remains `relation := no_claim`.
- `fidelity.human_review` remains `none`.
- Both `stability-mass-triangle` frontier records retain
  `discharged_by: null`. The machine correction changes their stale
  description and label; it does not perform the human discharge.
- Nothing identifies `AutPairQuot v` with the paper's literal `Aut(D)`.

## Adversarial checks

1. Confirm the new theorem elaborates only from the two named existing
   theorems and does not resolve through a hidden instance or new axiom.
2. Search the diff for any new `instance`, `letI`, or changed topology owner.
3. Verify that `PseudoEMetricSpace.ofEDistOfTopology` still retains the Section
   6 topology definitionally and that the new corollary does not create an
   instance diamond.
4. Review the complete HN dependency chain beneath
   `stabilityMassTriangleInequality`; do not treat the one-line corollary as
   independent evidence that the long proof is mathematically correct.
5. Compare the exact theorem statement with both clauses of the stored
   Proposition 8.1 quotation. Decide explicitly whether the source relation is
   faithful; do not infer it from compilation.
6. Confirm the registry remains blocked under E-05 until a named human review
   and owner acceptance are recorded.
7. Confirm `AutPairQuot v` caveats remain intact and independent of this issue.

## Expected mechanical evidence

- audit: 1,354 declarations, permitted axioms only, no `sorryAx`;
- census: 1,622 authored declarations; 114 private; 154 structure-field
  projections; zero authored public declarations outside the hand audit;
- gated split: 944 theorems, 40 structures, 370 other non-theorems;
- registry validator: 9/9 rules pass with the four-label allowlist;
- coverage map: unchanged;
- full build and environment linter: pass;
- `git diff --check`: pass.

The review should quote the exact reviewed commit SHA and the statements of
`stabilityMassTriangleInequality` and
`stabilityDistanceTopologyCompatible`. Only the owner may use that review to
fill `discharged_by` or change the Proposition 8.1 citation relation.
