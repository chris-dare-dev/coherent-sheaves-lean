# Issue #89 response to Fable adversarial review

Status: **ALL PRE-LANDING FINDINGS ADDRESSED; ADDITIVE STRENGTHENING DEFERRED**

This is a response to the independent machine review in
`2026-08-10-issue89-h0-exactness-fable-review.md`. It is not a human
source-faithfulness review, does not change `human_review: none`, and makes no
claim about a paper theorem.

The reviewed seven-declaration API is unchanged. The proof module is now 139
lines after removing four redundant proof-local instance declarations.

## Finding disposition

| finding | disposition |
|---|---|
| P2-1, stale `HeartTorsionPair` trust prose | Fixed. The module now preserves the true Mathlib boundary while recording the project-level generic cohomology theorem and anchor transport. |
| P2-2, stale injected-name registry and command | Fixed and remeasured. `HeartStabilityData` is listed, and the command scans all of `BridgelandStabLean/`. The broadened command also found three older `HNFiltration` extensions under `WeakStability/` that the review's proposed count missed, so the exact total is 31 rather than 28. |
| P2-3, stronger cokernel-comparison isomorphism | Deliberately deferred to follow-up issue [#133](https://github.com/chris-dare-dev/bridgeland-stab-lean/issues/133). It is additive, is not consumed by stale PR #103, and would change the reviewed public API and all count records. |
| P3-1, present-tense mass-triangle consumption | Fixed. The module and README now say the API is intended for the current-main rewrite of stale PR #103. |
| P3-2, construction/proof/transport attribution | Fixed. `formalization.yaml` names `Tilting/HeartCohomology.lean`, `Tilting/HeartCohomologyHomological.lean`, and `GroupAction/H0ExactnessBridge.lean` for their respective roles. |
| P3-3, redundant local instances | Fixed. The four shadowing `letI` lines were removed; the canonical global heart instances elaborate both proofs unchanged. |

## Post-fix snapshot

- base: `c7ad6ab249eb7f0a1b890a4c9ff5484b4091c7cf`;
- branch: `agent/issue-89-h0-exactness-current`;
- proof module SHA-256:
  `30cb01af16c335d2fdef3b452a7d51be33fe1a5513c85af9b6f00c54e04b963d`;
- tracked supporting-diff SHA-256:
  `713a4a571b0abbdde80622ff043e4d78323e20e5c96fb5ebb717c3070f8295dd`.

The original Fable handoff and review remain unedited evidence about the
pre-fix snapshot. Their old hashes should not be used to identify this
post-fix tree.

## Validation

Observed on the post-fix snapshot:

- focused bridge plus root build: success, 3,824 jobs;
- environment linter: passed;
- audit: 1,128 declarations, only `propext`, `Classical.choice`, and
  `Quot.sound`, no `sorryAx`;
- census: 1,325 authored declarations, 111 private, 86 structure-field
  projections, zero public declarations outside the audit;
- coverage: `{mapped: 1, target: 9}`;
- emitter build: success, 7,619 jobs;
- emission: 2,647 constants, 1,439 in scope, 1,208 internal, zero `sorryAx`;
- all eight emitted constants from the proof module (seven authored plus one
  generated proof constant) use only the allowed three axioms;
- `git diff --check`: clean.
