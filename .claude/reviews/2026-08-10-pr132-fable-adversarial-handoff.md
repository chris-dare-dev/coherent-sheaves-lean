# Fable adversarial review handoff — PR #132 weak charge rays and phase tilt

Status: **READY FOR INDEPENDENT ADVERSARIAL REVIEW**

This is a review brief, not a review verdict. It does not change
`formalization.yaml`'s `human_review: none`, does not promote the §14 coverage
coordinate beyond `mapped`, and must not be cited as human source-faithfulness
review. Fable's review is an independent machine review unless Chris Dare
separately performs and records the owner-only source judgement.

## Immutable review target

| item | value |
|---|---|
| repository | `chris-dare-dev/bridgeland-stab-lean` |
| merged PR | [#132](https://github.com/chris-dare-dev/bridgeland-stab-lean/pull/132) |
| pre-PR baseline | `8fc9773da19463d691b3cd3778e3b8665575b7ee` |
| PR theorem commit | `2829e8071b8f096c8e5bcd6b5772c05dd08dbc5f` |
| trust-note follow-up | `5edb2c567a8a50f621e03e75b7fbaf83f32426f6` |
| merge commit to review | `c7ad6ab249eb7f0a1b890a4c9ff5484b4091c7cf` |
| review delta | 8 files, 375 insertions, 61 deletions |
| GitHub CI | [merge run](https://github.com/chris-dare-dev/bridgeland-stab-lean/actions/runs/31451034804), success |
| Lean | `v4.29.0` |
| anchor | `BridgelandStability@9e48f23a382ba117b63076a33e0e775389fef1ba` |
| transitive Mathlib | `8a178386ffc0f5fef0b77738bb5449d50efeea95` |

The commit containing this handoff may later contain issue #89 work. That work
is **outside this review**. Detach at `c7ad6ab` and compare it only with
`8fc9773`; do not review a moving branch tip.

Useful first commands:

```bash
git fetch origin
git switch --detach c7ad6ab249eb7f0a1b890a4c9ff5484b4091c7cf
git status --short --branch
git diff --stat 8fc9773da19463d691b3cd3778e3b8665575b7ee c7ad6ab249eb7f0a1b890a4c9ff5484b4091c7cf
git diff 8fc9773da19463d691b3cd3778e3b8665575b7ee c7ad6ab249eb7f0a1b890a4c9ff5484b4091c7cf -- \
  BridgelandStabLean/WeakStability/ChargeRay.lean \
  BridgelandStabLean/WeakStability/TiltPreStability.lean
```

## Review request for Fable

Perform an independent mathematical, Lean-API, instance, and trust-record
review. Read the declarations and their dependencies; do not infer correctness
from this summary, successful elaboration, theorem names, or CI.

Do not edit during the first pass. For every substantive finding:

1. assign P0, P1, P2, or P3 severity;
2. cite the exact file and a narrow line range at `c7ad6ab`;
3. classify it as a mathematical error, statement-strength error, API/instance
   hazard, proof-maintenance hazard, or trust/prose error;
4. state which downstream declarations are affected;
5. give the smallest defensible correction.

If there are no findings, say so explicitly and list every declaration and
verification command actually inspected. Do not return only a green-build
summary.

Suggested terminal verdicts:

- `SHIP`: no substantive findings;
- `SHIP WITH FOLLOW-UPS`: no soundness blocker, but named nonblocking findings;
- `BLOCK`: at least one P0/P1 finding or an unresolved statement-strength issue.

## What PR #132 intends to establish

The PR closes the last analytic premise in the **phase-language** reverse weak
heart--slicing construction.

1. A complex number with positive imaginary part lies on the ray determined by
   the normalized weak phase

   ```text
   weakPhaseOfSlope μ = arctan μ / π + 1/2,
   μ = -Re(z) / Im(z).
   ```

   The radius is positive.
2. For a nonzero heart object at the phase-`1` boundary, the charge lies on the
   nonpositive real axis. The radius is nonnegative and may be zero, as weak
   stability permits zero charge at integer phases.
3. The ray identity transports through every integer shift, using the
   Grothendieck-group sign of a shift.
4. The integer-normalized ambient phase predicate constructed from any weak
   stability function therefore satisfies the charge-ray axiom required by a
   `WeakPreStabilityCondition`.
5. The already assembled phase-tilt heart HN, noetherian, support, Hom-vanishing,
   and ambient-HN results can consequently be packaged as an actual
   phase-language `WeakPreStabilityCondition` without an externally supplied
   compatibility proof.

## What PR #132 deliberately does not establish

The review should reject any prose or theorem that crosses these boundaries:

- It does not declare or source-bind Proposition 14.16.
- It does not promote `sec-14-weak-stability-tilting` beyond `mapped`.
- It does not constitute a dated human reading of the exact slope-cutoff
  statement in `1902.08184v4`.
- It does not state the paper-facing cutoff equivalence for display (14.1).
- It does not prove Lemmas 14.8 or 14.11 or decide the `ℚ[i]`-discreteness
  hypothesis recorded for them.
- It does not identify the heart's Grothendieck group with the ambient `K₀ C`.
- It does not add geometric substrate or make a claim about `Coh(X)`.
- It proves the normalized slope/phase relation in the charge-ray form needed
  by the constructor. It does **not** expose a standalone theorem literally
  written as `μ = -cot (πφ)`.

The last distinction is a deliberate prose-review target. README says the
identity is proved “in the form needed here.” Check that this wording does not
overstate the actual ray theorem.

## Public declaration inventory

The PR adds eleven audited public declarations: nine theorems and two
constructions. It removes the former `compat` structure projection from
`PhaseTiltPreStabilityObligations`.

### `WeakStability/ChargeRay.lean`

1. `complex_eq_pos_mul_exp_weakPhaseOfSlope`
2. `WeakStabilityFunction.charge_ray_of_mem_heart`
3. `negOnePow_mul_exp_pi_eq_exp_add_int`
4. `WeakStabilityFunction.ambientPhasePredicate_charge_ray`

### `WeakStability/TiltPreStability.lean`

5. `WeakPreStabilityCondition.phaseTilt_ambientPhasePredicate_charge_ray`
6. `PhaseTiltHeartObligations.toWeakPreStabilityCondition`
7. `PhaseTiltHeartObligations.toWeakPreStabilityCondition_Z`
8. `PhaseTiltHeartObligations.toWeakPreStabilityCondition_P`
9. `phaseTiltWeakPreStabilityConditionOfTiltingProperty`
10. `phaseTiltWeakPreStabilityConditionOfTiltingProperty_Z`
11. `phaseTiltWeakPreStabilityConditionOfTiltingProperty_P`

Also inspect the changed definition of
`PhaseTiltPreStabilityObligations`: it now retains only the `heart` field and
delegates to the direct heart constructor. Confirm that removing `compat` is
mathematically justified rather than merely source-compatible with the current
call sites.

## Adversarial proof map

### A. Finite slope and analytic signs

The proof chooses

```text
μ = -Re(z) / Im(z)
s = sqrt(1 + μ²)
m = Im(z) * s.
```

Attack the following points:

- confirm `m > 0` from `Im(z) > 0` without a hidden zero denominator;
- check the angle identity
  `π(arctan μ / π + 1/2) = arctan μ + π/2`;
- check the `Real.sin_arctan` and `Real.cos_arctan` algebra in both real and
  imaginary components;
- verify the sign convention with concrete samples:
  `z = i` gives phase `1/2`, `z = -1+i` gives phase `3/4`, and
  `z = 1+i` gives phase `1/4`;
- check that the theorem proves equality in the direction later rewrites need.

### B. The weak phase-`1` boundary

For `Im Z(E) = 0` and `Re Z(E) ≤ 0`, the proof takes `m = -Re Z(E)`.

Attack these cases separately:

- `Re Z(E) < 0`: the ray is the negative real axis and the radius is positive;
- `Z(E) = 0` with nonzero `E`: the radius is zero and this is allowed only
  because phase `1` is an integer;
- the strict-radius implication is discharged by showing phase `1` contradicts
  “phase is not an integer.” Confirm there is no accidental proof of strict
  positivity for a zero charge.

### C. Arbitrary integer shifts

This is the highest-risk part of the PR. Check it for `n = 1`, `n = -1`, and
one nontrivial even shift.

- Verify
  `(-1)^(Int.natAbs n) * exp(π i ψ) = exp(π i (ψ+n))`
  for negative as well as positive `n`.
- Confirm `Int.cast_negOnePow` and `Complex.exp_int_mul` are used with the
  correct orientation.
- Check `H = E⟦-n⟧` and the isomorphism `H⟦n⟧ ≅ E`; reverse either one and the
  phase law still looks plausible while being wrong.
- Check the class identity
  `K₀.of E = (-1)^|n| • K₀.of H` against `K₀.of_shift_int`.
- Check `phaseBase_add_phaseIndex` at positive, zero, and negative integer
  phases, where the normalized base lies on the phase-`1` boundary.
- Check the proof that a noninteger ambient phase implies the normalized heart
  phase is noninteger.
- Confirm the zero-object disjunct of `ambientPhasePredicate` is eliminated
  only by the explicit `¬ IsZero E` premise.

### D. Rotation by the phase cutoff

`phaseTilt_ambientPhasePredicate_charge_ray` is a short `simpa`, so its risk is
in definitional alignment rather than proof length.

- Expand `phaseTiltLatticeCharge_apply` and
  `phaseTiltWeakStabilityFunction_charge` and verify that both use the same
  rotation `exp(-π i β)`.
- Check that the phase stored by the tilted weak stability function matches the
  rotated charge rather than the unrotated source charge.
- Check endpoint assumptions: the ray theorem accepts `0 ≤ β < 1`; the direct
  constructor from `TiltingProperty` requires `0 < β < 1` because the heart
  assembly is stronger.

### E. Reverse weak prestability packaging

- Read `reverseSlicingObligationsOfHN` and
  `ReverseSlicingObligations.toWeakPreStabilityCondition`; confirm every
  `WeakPreStabilityCondition` field is supplied rather than hidden behind an
  unexpectedly strong instance.
- Confirm `PhaseTiltHeartObligations.ambientHN` genuinely supplies HN towers
  for all ambient objects using boundedness, not merely tilted-heart objects.
- Check that Hom vanishing comes from the ambient phase construction already
  proved upstream and is not silently assumed in the new definition.
- Confirm the `_Z` and `_P` projection theorems are definitionally correct and
  do not mask a mismatch introduced by proof irrelevance.
- Trace `Zlin`, `hcompat`, and `hsupport` through
  `phaseTiltHeartObligationsOfTiltingProperty`. The output charge is the
  rotated `sigma.Z`; `Zlin` is the linear realization used to state support.
  Verify `hcompat` is enough to connect them.
- Inspect every `omit [FiniteDimensional ℝ V]` and confirm the omitted instance
  is genuinely unused rather than being recovered transitively.

### F. API and downstream compatibility

- Search the full environment, not just the source tree, for consumers of the
  removed `PhaseTiltPreStabilityObligations.compat` projection.
- Check whether retaining the now-one-field obligation wrapper is useful
  compatibility or misleading duplication.
- Check imports for a cycle or unnecessary exposure introduced by adding
  `ChargeRay.lean` to the root module.
- Confirm no global instance was added by this PR.

### G. Trust records and prose

Inspect all six non-proof files in the delta:

- `BridgelandStabLean.lean`
- `WeakStability/TiltingProperty.lean`
- `README.md`
- `formalization.yaml`
- `registry/coverage-1902.08184v4.json`
- `scripts/Audit.lean`

Required checks:

- coverage remains `{mapped: 1, target: 9}`;
- no dated source review or owner signoff is inferred;
- Proposition 14.16 remains undeclared;
- the registry note no longer falsely says the reverse constructor is absent;
- “formalizes `μ = -cot(πφ)` in the form needed” is no stronger than the
  theorem actually proved;
- all eleven public declarations are audited, and the removed projection is
  not counted as a live declaration;
- census numbers distinguish theorems, constructions, private declarations,
  and structure projections exactly as the audit prose claims.

## Reproduction commands

Run from a clean detached checkout at `c7ad6ab`:

```bash
lake build
lake exe runLinter BridgelandStabLean
lake env lean scripts/Audit.lean > audit.txt 2>&1
python3 scripts/check_audit.py audit.txt
python3 scripts/check_coverage_map.py
git diff --check 8fc9773da19463d691b3cd3778e3b8665575b7ee c7ad6ab249eb7f0a1b890a4c9ff5484b4091c7cf
lake build emit
lake exe emit --out attest/lean-emission.json
```

Then inspect the emission rather than trusting exit text:

```bash
python3 - <<'PY'
import json
d = json.load(open("attest/lean-emission.json", encoding="utf-8"))
print("constants", len(d["constants"]))
print("in_scope", d["counts"]["in_scope"])
print("sorryAx", sum("sorryAx" in c["axioms"] for c in d["constants"]))
PY
```

## Evidence already observed by the authoring session

These are claims to reproduce, not substitutes for independent review:

- `lake build`: 3,823 jobs, success;
- environment linters: no findings;
- audit checker: 1,121 listed declarations, all within the allowlist;
- environment census: 1,318 authored declarations, 111 private,
  86 structure projections, zero authored public declarations outside the
  audit;
- coverage checker: `{mapped: 1, target: 9}`;
- emitter: 2,639 constants, 1,432 in scope, zero `sorryAx`;
- GitHub merge run 31451034804: all build, audit, linter, no-`sorry`, emitter,
  and artifact
  steps completed successfully.

Again: these results address elaboration, axioms, hygiene, and inventory. They
do not establish mathematical correctness or source faithfulness.

## Requested review output

Please return a document with:

1. the immutable target SHA and baseline SHA;
2. a verdict (`SHIP`, `SHIP WITH FOLLOW-UPS`, or `BLOCK`);
3. findings ordered by severity with exact line references;
4. a declaration-by-declaration checklist for all eleven public declarations;
5. explicit confirmation or rejection of boundaries A–G above;
6. commands actually run and their observed outputs;
7. a separate section titled **Source-faithfulness not adjudicated** unless a
   human owner performs that review under the registry protocol.

Do not update `human_review`, the §14 coverage status, or the declaration names
as part of the first-pass adversarial review.
