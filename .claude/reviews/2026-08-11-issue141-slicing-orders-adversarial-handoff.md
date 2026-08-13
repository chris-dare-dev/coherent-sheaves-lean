# Destination issue #211 (source issue #141) adversarial handoff — slicing orders, Bayer, cofiltration

Date: 2026-08-11
Branch: `agent/issue-141-slicing-orders`
Base: `87279440a8056781e31ecd1fd7a229efe92bd7b8` (main after PR #149)
Scope: reviewable abstract theorem slice of destination issue #211, transferred from source issue #141; this does not close the epic

## What this branch claims

- `Slicing.Precedes` is `P₁(phi) <= P₂(< phi)`.
- `Slicing.PrecedesWeak` is `P₁(phi) <= P₂(<= phi)`.
- The four formulations in arXiv:2607.28411v1, Lemma 3.13, are separate iff
  theorems for both strict and weak orders.
- The weak relation is reflexive; both relations are transitive; strict/weak
  mixed transitivity holds; and `P ≺ P[1]`.
- Simultaneous autoequivalence transport preserves both relations, including
  the action of `AutPairQuot v` on class-map stability conditions.
- A hypothesis-carrying preimage package proves that any future pullback or
  pushforward slicing construction preserving phase slices and strict/weak
  upper windows preserves the corresponding order. No geometric functor is
  manufactured by this interface.
- `BayerProperty` is the comparison `P_sigma ⪯ P_(q • sigma)[l]` for a fixed
  `AutPairQuot v` and fixed integer; `SlicingBayerProperty` is its reusable
  `AutQuot C`-level abstraction.
- The two intrinsic Lemma 3.17 phase formulations are proved for arbitrary
  quotient representatives: inverse-image `phiPlus` with the `[-l]` shift
  moved into the inequality, and forward-image `phiMinus` with `[l]` encoded
  as the equivalent lower bound `phi - l`.
- `CofiltrationProperty` models the categorical content of Definition 3.22:
  a finite distinguished-triangle sequence, positive finite-biproduct
  multiplicities, terminal zero object, and final shifted cone in
  `t.le (-N)`. The `N = infinity` case requires the last cone itself to be
  zero and implies every finite bound.
- Li's names are aliases of these same two relations, with explicit iff
  comparison theorems.

## What this branch does not claim

- It does not formalize schemes, line bundles, tensor autoequivalences,
  pullback/pushforward slicings, base change, or moduli.
- It does not prove the geometric filtration property (Definition 3.19) or
  Propositions 3.21, 3.24, 3.26, or 3.27.
- It does not bind `@[cites]` or assert source-faithfulness.
- `registry/coverage-2607.28411.json` is deliberately all `target`; only the
  landing PR may propose the issue-prescribed §3.4 `target -> mapped` change.

## Source coordinates checked

Checked directly against arXiv:2607.28411v1 on 2026-08-11:

- Definition 3.12: strict and weak slicing relations.
- Lemma 3.13: all four strict and all four weak formulations.
- Remark 3.14: transitivity, autoequivalence invariance, conditional
  pullback/pushforward behavior.
- Definition 3.16 and Lemma 3.17: Bayer property and its phase formulations.
- Definition 3.22: finite and infinity cofiltration clauses.

Pinned PDF downloaded 2026-08-11:

- SHA-256: `f8770154235fe2c82698513b4633b3ee509fa11f722190a4c9f573fca589a98c`
- bytes: `811269`
- margin banner: `arXiv:2607.28411v1 [math.AG] 30 Jul 2026`

## Files to review

- `BridgelandStabLean/StabilityCondition/Phase/Order/Basic.lean`
- `BridgelandStabLean/StabilityCondition/Phase/Order/Characterizations.lean`
- `BridgelandStabLean/StabilityCondition/Phase/Order/Functoriality.lean`
- `BridgelandStabLean/StabilityCondition/Phase/Order/Equivariance.lean`
- `BridgelandStabLean/StabilityCondition/Phase/Order/Bayer.lean`
- `BridgelandStabLean/StabilityCondition/Phase/Order/Cofiltration.lean`
- `registry/coverage-2607.28411.json`
- `scripts/check_coverage_map.py`

## Adversarial questions

1. Are the strict inequalities oriented correctly in all four Lemma 3.13
   formulations, especially the right-semistable `phi < phiMinus` direction?
2. Do the proofs of the lower-phase and endpoint formulations use only valid
   nonzero-factor properties, with no hidden choice of a zero HN factor?
3. Is `precedes_phaseShift_one` consistent with this repository's convention
   `P[1](phi) = P(phi + 1)`?
4. Does transport through `mapEquiv` preserve `ltProp` and `leProp` exactly,
   including both zero-object branches and the unit/counit orientations?
5. Does the `AutPairQuot` theorem say only what its action establishes, without
   identifying `AutPairQuot v` with `Aut(D)`?
6. Is the Bayer property quantifier order faithful, and is using an arbitrary
   `AutQuot C` an honest abstraction of tensoring by one chosen line bundle?
7. Does `CofiltrationData` encode `m+1` composable arrows, with the first `m`
   cone fibres prescribed and the final cone bounded, without an off-by-one?
8. Is `CofiltrationPropertyInfinity` correctly attached to the unshifted last
   cone rather than merely to its shift?
9. Are any docstrings stronger than the Lean statements, particularly around
   the geometric propositions intentionally left out?
10. Does `SlicingOrderPreimageData` state a sufficient and honest conditional
    version of Remark 3.14(3), without implying that a geometric pullback or
    pushforward was constructed?
11. Do the representative Bayer formulas correctly account for the inverse
    twist and integer shifts in Lemma 3.17(2)/(3), including the unit/counit
    orientations used in the forward-image lower-phase proof?
12. Should the landing promote only the §3.4 near-term coordinate to `mapped`,
    and if so is the proposed review evidence sufficient under repository
    governance?

## Reproduction

```sh
lake build BridgelandStabLean
lake exe runLinter BridgelandStabLean
lake env lean scripts/Audit.lean > audit.txt 2>&1
python3 scripts/check_audit.py audit.txt
lake env lean scripts/Census.lean
python3 scripts/check_coverage_map.py
python3 scripts/check_coverage_map.py registry/coverage-2607.28411.json
git diff --check
rg -n '\b(sorry|admit|axiom)\b' BridgelandStabLean/StabilityCondition/Phase/Order
```

Expected census after the conditional transport and Lemma 3.17 extension:

- 125 modules;
- 1703 authored declarations;
- 114 private declarations, 100 theorems;
- 167 structure projections;
- 1417 hand-audited public declarations;
- five pre-existing generated `HeartAbelian` companions outside the audit;
- no declaration introduced by this branch outside the audit.

Local observations already made: 3883-job library build green; environment
linter green; both coverage validators green; diff check green; and the final
single-threaded exact audit covered all 1417 commands within the repository
allowlist with no `sorryAx`. Earlier concurrent audit attempts were externally
terminated and the truncation guard correctly rejected those prefixes.

## Landing-time promotion proposal (not applied)

The branch deliberately leaves `sec-3-4-bayer-property` at `target`. If an
independent review accepts the source coordinates and the theorem orientations,
the landing PR may propose the issue-prescribed `target -> mapped` change using
that dated verdict as evidence. Neither this authoring handoff nor CI is an
independent source-faithfulness review, so neither is sufficient on its own.
