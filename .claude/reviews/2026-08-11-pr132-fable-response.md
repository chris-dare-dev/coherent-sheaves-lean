# Response to the PR #132 Fable adversarial review

Status: **ALL FOLLOW-UPS ADDRESSED**

This is a maintainer response to an independent machine review. It is not a
human source-faithfulness review, does not change `human_review: none`, and does
not promote `sec-14-weak-stability-tilting` beyond `mapped`.

## Review target

- reviewed merge: `c7ad6ab249eb7f0a1b890a4c9ff5484b4091c7cf`
- baseline: `8fc9773da19463d691b3cd3778e3b8665575b7ee`
- verdict received: `SHIP WITH FOLLOW-UPS`
- corrective branch: `agent/pr132-adversarial-followups`

## Disposition

1. **F1, stale `PhaseTiltHeartObligations` docstring — fixed.** The structure
   is now described truthfully as the heart-level input to the ambient
   constructor; it makes no paper-level source claim.
2. **F2, incorrect historical emitter counts — fixed.** The handoff now records
   2,639 raw constants, 1,432 in scope, and zero `sorryAx` at `c7ad6ab`.
3. **F3, redundant one-field wrapper — fixed.** The
   `PhaseTiltPreStabilityObligations` structure, its projection, and its three
   public conversion declarations are deleted. Their audit entries are also
   removed.
4. **F4, unnecessarily strong direct-constructor premises — fixed.** The new
   theorem `phaseTilt_hasHNPropertyOfTiltingProperty` isolates exactly the HN
   consequence of Definition 14.12. The direct weak-prestability constructor
   and its `Z`/`P` lemmas now require only `htilt`; `Zlin`, charge compatibility,
   and support are no longer premises.
5. **F5, overstrong cotangent prose — fixed.** The corrective commit split the
   finite-branch cotangent statement from the boundary ray statement. The
   concurrent current-main README rewrite removes the detailed claim entirely.
6. **F6, branch CI cited for the merge — fixed.** The handoff now cites the
   successful merge run `31451034804`.

## Measured trust surface after the correction

After reconciliation with the concurrent current-main taxonomy merge,
`scripts/Census.lean` reports:

- 1,382 authored declarations;
- 1,188 declarations named by `scripts/Audit.lean`;
- 109 private declarations and 85 structure projections outside that list;
- 846 gated theorems, 19 gated structures, and 323 other gated
  non-theorems;
- zero authored public declarations outside the hand audit.

The taxonomy merge initially exposed 60 unaudited public declarations in the
expanded cohomological-exactness and mass-triangle modules. They are now named
by the audit and subjected to its axiom gate; this is an inventory correction,
not a review of those concurrent mathematical changes.

The independent environment emitter reports 2,759 constants, 1,492 in scope,
12 cited declarations, and zero constants whose axiom closure contains
`sorryAx`.

The corrective commit, PR, and Linux CI run are recorded in GitHub's immutable
history. No source-faithfulness or registry-status conclusion is inferred from
these maintenance results.
