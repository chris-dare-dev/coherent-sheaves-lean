# Issue #81 adversarial review handoff — source-facing §14 completion

Date: 2026-08-11

Repository: `chris-dare-dev/bridgeland-stab-lean`

Branch: `agent/issue-81-source-facing`

Base: `origin/main` at `901279b96298855f4a1af8f825ef58bcd63f7234`

Source: arXiv:1902.08184v4, pinned by
`registry/coverage-1902.08184v4.json`; review pp. 71–74, especially display
(14.1), Definition 14.12, Proposition 14.16, and Lemma 14.17.

## Requested verdict

Please return one of `SHIP`, `SHIP WITH FIXES`, or `DO NOT SHIP`, separating:

1. Lean soundness and API correctness;
2. fidelity to the pinned v4 statements;
3. whether the registry should remain `mapped` (the proposed PR intentionally
   leaves it there);
4. any premise that is stronger or weaker than the source.

Do not infer fidelity merely from a clean build or axiom audit.

## New source-facing surface

### Display (14.1)

File:
`BridgelandStabLean/StabilityCondition/Weak/Tilting/TorsionPair/SourceSlope.lean`

Review:

- `ExtremalHNData`, `muPlus`, and `muMinus` choose nonzero endpoint factors.
- `weakPhaseOfSlope_muPlus` and `weakPhaseOfSlope_muMinus` prove that their
  normalized phases are the intrinsic slicing endpoints, so the choice must
  not affect the resulting comparisons.
- `muMinus_gt_iff_phiMinus_gt` and `muPlus_le_iff_phiPlus_le` are the critical
  order translations.
- `slopeTorsionPair`, its two projection theorems, and
  `slopeTilt_heart_iff` are the claimed source-facing form of display (14.1).

Adversarial question: does the source use exactly the same strict/non-strict
boundary convention at finite slope `b`?

### Exact charge normalization

File:
`BridgelandStabLean/StabilityCondition/Weak/Tilting/Source/Charge.lean`

Review:

- `sourceTilt_multiplier` proves
  `1/(i-b) = (1/sqrt(1+b²)) exp(-π i slopeCutPhase(b))`.
- `sourceTiltWeakStabilityFunction` has charge definitionally `Z/(i-b)`.
- slope, semistability, stability, zero charge, and the ambient phase
  predicate are transported through the positive scale.
- `sourceTiltWeakPreStabilityConditionOfTiltingProperty` has the exact lattice
  charge and its `P_source` theorem identifies its slices with the exact
  source-normalized weak function.

Adversarial questions:

- Check the sign of `i-b`, the direction of rotation, and the positive scale.
- Check the phase-one/zero-charge boundary; no cotangent identity is claimed
  there.
- Check that the ambient predicate equality really closes the integration
  between the returned weak prestability condition and the explicit tilted
  heart function.

### Proposition 14.16 candidate

Files:

- `BridgelandStabLean/StabilityCondition/Weak/Tilting/Source/Support.lean`
- `BridgelandStabLean/StabilityCondition/Weak/Tilting/Source/Theorems.lean`

Review `sourceTiltConclusion`. It packages:

- the exact source-normalized weak prestability condition;
- support for semistable classes in the explicit tilted heart;
- a `NoetherianTorsionSubcategory` on the slope-cut tilted heart;
- equality of its torsion class with exact source zero charge.

Adversarial questions:

- Does the repository's heart-level `HasSupportProperty` have precisely the
  same mathematical force as the paper's slicing-level support convention?
- Is `SourceTiltConclusion.condition_eq` useful dependent packaging, or does
  it hide an identification that should instead be a theorem?
- Is the noetherian object constructed on definitionally the same heart as
  the weak condition's standard heart?

### Lemma 14.17 candidate

File:
`BridgelandStabLean/StabilityCondition/Weak/Tilting/Source/Theorems.lean`

Review:

- `sourceTiltWeakStabilityFunction_isSemistable_iff_classification` separates
  the two cases by the sign of the original imaginary charge.
- `hom_eq_zero_of_zeroCharge_to_sourceTiltSemistable` is the positive-new-
  imaginary/stable refinement for the exact source charge.

Important possible fidelity seam: the second branch reuses
`IsPhaseTiltTypeTwo`. That predicate explicitly stores `phaseFree U` and the
positive-imaginary Hom-vanishing implication. The printed Lemma 14.17 only
describes an extension by an original semistable `U` and states Hom vanishing
afterwards as a `moreover` conclusion. Determine whether the stored fields are
automatically forced by `E` belonging to the tilted heart and the other source
hypotheses. If not, this theorem is a strengthened candidate rather than the
literal biconditional and must not be promoted.

## Deliberate non-claims

- The registry remains `mapped`; no `reviewed` or `formalized` promotion is in
  this branch.
- Lemmas 14.8 and 14.11 remain undeclared under issue #108's documented
  blocker policy; this branch does not pretend otherwise.
- No §14.3 geometry or base change is introduced.
- No boundedness or moduli statement follows from support.

## Mechanical evidence

Run from the repository root:

```bash
lake build
lake exe runLinter BridgelandStabLean
lake env lean scripts/Audit.lean
python3 scripts/check_coverage_map.py
lake env lean scripts/Census.lean
```

Observed before handoff:

- full build: pass;
- 16 environment linters: pass;
- all newly audited declarations depend only on `propext`,
  `Classical.choice`, and `Quot.sound`;
- coverage validator: pass with `{mapped: 1, target: 9}`;
- census: zero authored public declarations outside the hand audit.

## Suggested attack order

1. Compare the four source coordinates directly to v4.
2. Try to falsify the cutoff inequalities at `b < 0`, `b = 0`, and `b > 0`.
3. Recalculate the complex multiplier independently.
4. Audit the type-two reverse implication and the stable refinement.
5. Check the returned condition/support/noetherian objects inhabit the same
   mathematical heart, not merely isomorphic-looking types.
6. Only then assess whether any registry promotion could be proposed.
