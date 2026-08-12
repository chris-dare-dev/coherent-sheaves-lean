# Fable adversarial review handoff — issue #89 H⁰ exactness bridge

Status: **READY FOR INDEPENDENT ADVERSARIAL REVIEW OF THE LOCAL SNAPSHOT**

This is a review brief, not a review verdict. It does not change
`formalization.yaml`'s `human_review: none`, establish source faithfulness, or
close issue #89 by itself. Fable's review is an independent machine review
unless Chris Dare separately performs and records the owner-only judgement.

## Review target

The implementation is complete locally but is not yet committed because the
repository's authenticated GitHub publishing workflow is blocked by an invalid
local `gh` credential. Review this exact snapshot:

| item | value |
|---|---|
| repository | `chris-dare-dev/bridgeland-stab-lean` |
| worktree | `/Users/chris.dare/Personal/SourceCode/bridgeland-stab-lean-weak-heart-equivalence` |
| branch | `agent/issue-89-h0-exactness-current` |
| base / current `HEAD` | `c7ad6ab249eb7f0a1b890a4c9ff5484b4091c7cf` |
| issue | [#89](https://github.com/chris-dare-dev/bridgeland-stab-lean/issues/89) |
| stale draft being superseded | [PR #100](https://github.com/chris-dare-dev/bridgeland-stab-lean/pull/100) |
| new proof module | 143 lines, 7 public declarations |
| proof-module SHA-256 | `b001c100192b422114edf1ebd26b91dc3912b13309f243ca19e1e14de236a7f6` |
| tracked supporting-diff SHA-256 | `7b9a08a6a9efa6533d9ac284519fc795b376289e22b4c6fb5447f4310c1d60c5` |
| Lean | `v4.29.0` |
| anchor | `BridgelandStability@9e48f23a382ba117b63076a33e0e775389fef1ba` |
| transitive Mathlib | `8a178386ffc0f5fef0b77738bb5449d50efeea95` |

The tracked supporting-diff digest covers exactly:

- `BridgelandStabLean.lean`
- `README.md`
- `formalization.yaml`
- `scripts/Audit.lean`

The proof-module digest covers
`BridgelandStabLean/GroupAction/H0ExactnessBridge.lean`. The review handoff
files themselves are outside the proof delta and the audit census.

Verify the snapshot before reviewing:

```bash
cd /Users/chris.dare/Personal/SourceCode/bridgeland-stab-lean-weak-heart-equivalence
test "$(git rev-parse HEAD)" = c7ad6ab249eb7f0a1b890a4c9ff5484b4091c7cf
test "$(git branch --show-current)" = agent/issue-89-h0-exactness-current
shasum -a 256 BridgelandStabLean/GroupAction/H0ExactnessBridge.lean
git diff --binary -- BridgelandStabLean.lean README.md formalization.yaml \
  scripts/Audit.lean | shasum -a 256
git status --short
```

If either digest differs, stop and ask for a newly pinned handoff rather than
reviewing a moving target.

## Review request for Fable

Perform an independent mathematical, Lean-API, instance, dependency, and trust
review. Do not infer correctness from theorem names, elaboration, this summary,
or the green validation commands.

Do not edit during the first pass. For every substantive finding:

1. assign P0, P1, P2, or P3 severity;
2. cite an exact file and narrow line range;
3. classify it as a mathematical error, statement-strength error, API/instance
   hazard, dependency hazard, proof-maintenance hazard, or trust/prose error;
4. name the downstream declarations affected;
5. propose the smallest defensible correction.

If there are no findings, explicitly list all seven declarations and all
verification commands actually inspected. Do not return only “builds green.”

Suggested terminal verdicts:

- `SHIP`: no substantive findings;
- `SHIP WITH FOLLOW-UPS`: no soundness blocker, but named nonblocking findings;
- `BLOCK`: a P0/P1 finding or unresolved statement-strength/instance issue.

## Intended result

Current `main` already proves that the t-structure-only degree-zero cohomology
functor `originalHeartCohFunctor t 0` is homological. The anchor independently
defines `HeartStabilityData.H0Functor` from the same truncation-and-lift
expression. Issue #89 needs the anchor-facing API used by the mass argument,
not another proof of generic t-structure homologicality.

The new module therefore establishes only this chain:

```text
HeartStabilityData.H0Functor
  ≅ originalHeartCohFunctor h.t 0              (definitional identity)
  is homological                               (transport generic theorem)
  ≅ HeartStabilityData.H0primeFunctor          (anchor natural isomorphism)
  maps heart-source triangles to Exact H⁰ complexes
  implies Mono(coker(A → H⁰X₂) → H⁰X₃).
```

For a distinguished triangle

```text
A → X₂ → X₃ → A[1],     A in the original heart,
```

the conclusion is exactness at `H⁰(X₂)`. It is deliberately not a claim that
`A → H⁰(X₂)` is monic or that the three-term sequence is short exact.

## Explicit non-results

Reject any theorem or prose that crosses one of these boundaries:

- no mass triangle inequality is proved;
- no global mass theorem or global mass API is added;
- no new global `Functor.IsHomological` instance is installed;
- no source theorem from the pinned paper is declared or promoted;
- no §14 coverage status changes;
- no claim that the first H⁰ map is always monic;
- no claim that the induced three-term sequence is `ShortExact`;
- no wholesale port of PR #100's 692-line duplicate proof;
- no conclusion about stale PR #103 beyond supplying the narrow theorem shape
  needed by its future current-main rewrite.

## Public declaration inventory

All declarations are in namespace
`CategoryTheory.Triangulated.HeartStabilityData`.

Constructions:

1. `H0FunctorIsoOriginalHeartCohFunctor`
2. `heartSourceH0Complex`

Theorems:

3. `H0Functor_isHomological_unconditional`
4. `H0primeFunctor_isHomological_unconditional`
5. `heartSourceH0Complex_exact_iff_mono_cokernelDesc`
6. `heartSourceH0Complex_exact`
7. `mono_heartSourceH0primeShortComplex_cokernelDesc_unconditional`

## Adversarial proof map

### A. Definitional identification

The first declaration is `Iso.refl _`, not an isomorphism assembled from
components. Expand both functors and check that they are genuinely
definitionally equal:

```text
h.H0Functor
originalHeartCohFunctor h.t 0
```

Attack these points:

- confirm both lift exactly `h.t.truncGELE 0 0 ⋙ shiftFunctor C 0`;
- confirm they target the same full heart subcategory, with no transported or
  merely equivalent t-structure hidden in either definition;
- confirm reducibility is not masking a proof-irrelevant mismatch that could
  change after elaboration;
- temporarily replace `Iso.refl _` with an explicit type annotation if needed
  to see which definitional reductions Lean performs.

A failure here invalidates every downstream transport.

### B. Homologicality transport and instance hygiene

`H0Functor_isHomological_unconditional` locally installs the already-proved
generic value and transports it with `Functor.IsHomological.of_iso`.

- Check the orientation of `.symm`: the available instance is on
  `originalHeartCohFunctor`, while the result is for `h.H0Functor`.
- Check that “unconditional” means “no homologicality premise supplied by the
  caller,” not “no categorical hypotheses.”
- Search for top-level `instance` declarations in the new module. There should
  be none; the two `letI` declarations must remain proof-local.
- Confirm importing the module does not create a competing or looping global
  instance for the anchor functor.
- Check that `H0primeFunctor_isHomological_unconditional` transports along
  `H0FunctorIsoH0primeFunctor` in the correct direction.

### C. The exact complex

`heartSourceH0Complex` is an abbreviation for the anchor's existing
`heartSourceH0primeShortComplex`, with the zero-composition witness extracted
from distinguishedness.

- Verify the object and arrow order is `H⁰(A) → H⁰(X₂) → H⁰(X₃)`.
- Verify `A` is a heart object and is coerced to the ambient category in the
  triangle exactly once.
- Check `comp_distTriang_mor_zero₁₂` produces the orientation required by the
  short-complex constructor.
- Check that using `H0primeFunctor` is only a proof-normal-form choice and does
  not change the mathematical cohomology objects.

### D. Exact versus short exact

This is the highest-risk statement-strength boundary.

- Expand `ShortComplex.Exact`: it asserts exactness at the middle object.
- Confirm `Functor.map_distinguished_exact` gives exactly that proposition for
  `H0primeFunctor`.
- Confirm `heartSourceH0primeShortComplexIso` identifies the mapped triangle
  complex with the declared complex in the correct direction.
- Trace the long exact sequence immediately before `A → H⁰(X₂)`: the incoming
  map from `H⁻¹(X₃)` explains why the first map need not be monic.
- Search the new module, README, audit prose, and trust record for
  `ShortExact`; every occurrence must be a denial, not an asserted result.

### E. Cokernel comparison

The final consumer-facing result uses the abelian-category equivalence
`exact_iff_mono_cokernel_desc`.

- Verify the locally selected heart `Abelian` and limits instances are the
  canonical ones for `h.t.heart.FullSubcategory`.
- Expand `heartSourceH0primeShortComplex_cokernelDesc` and confirm its source
  is the cokernel of the first H⁰ arrow and its target/map are the intended
  third object/descended second arrow.
- Check that the `iff` is applied in the exact-to-mono direction in the final
  theorem.
- Ensure no epimorphism or cokernel-isomorphism conclusion is smuggled into the
  API by typeclass inference.

### F. Dependency and stale-PR reduction

PR #100 carried a 692-line duplicate homologicality development on a stale
stack. Current main already has
`Tilting.originalHeartCohFunctor_isHomological`; the new module is 143 lines.

- Confirm every imported module is needed and no import cycle is introduced.
- Compare against PR #100 to ensure no still-required consumer theorem was
  accidentally dropped.
- Inspect stale PR #103's actual use: it needs the value
  `hd.H0Functor_isHomological_unconditional` for a local instance. Confirm the
  new signature satisfies that shape without adding extra premises.
- Reject requests to port unused PR #100 helper lemmas merely for name parity.

### G. Trust records and counts

Inspect `README.md`, `formalization.yaml`, and `scripts/Audit.lean`.

- measured delta must be 7 public declarations: 5 theorems, 2 constructions;
- audit must report 1128 gated declarations, 793 theorems, 335 non-theorems;
- census must report 1325 authored declarations, 111 private, 86 structure
  projections, and 0 public declarations outside the audit;
- coverage must remain `{mapped: 1, target: 9}`;
- the two stale trust statements saying anchor H⁰ was never unconditionally
  homological must be corrected without rewriting the historical reason the
  aisles use Hom-orthogonality;
- no human review, paper theorem, or mass theorem may be inferred.

Remember that clean `#print axioms` output for the two constructions says only
that the constructions are axiom-clean; it does not turn them into theorems.

## Validation already observed locally

The following completed successfully on this snapshot:

```bash
lake build BridgelandStabLean.GroupAction.H0ExactnessBridge BridgelandStabLean
lake build
lake exe runLinter BridgelandStabLean
lake env lean scripts/Audit.lean > /private/tmp/issue89-audit.txt 2>&1
python3 scripts/check_audit.py /private/tmp/issue89-audit.txt
lake env lean scripts/Census.lean
python3 scripts/check_coverage_map.py
lake build emit
lake exe emit --out /private/tmp/issue89-lean-emission.json
git diff --check
```

Observed results:

- focused and full builds: success, 3824 jobs;
- environment linters: pass;
- hand audit: 1128 declarations, permitted axioms only, no `sorryAx`;
- census: 1325 authored, 111 private, 86 projections, 0 public audit gap;
- coverage registry: `{mapped: 1, target: 9}`;
- emitter: 2647 constants scanned, 1439 in scope, zero `sorryAx`;
- whitespace check: pass.

Re-run the commands. Treat them as reproducibility and hygiene evidence, not as
a substitute for the requested statement-strength and instance review.

## Required review output

Return:

1. terminal verdict: `SHIP`, `SHIP WITH FOLLOW-UPS`, or `BLOCK`;
2. findings ordered by severity, with exact locations;
3. declaration-by-declaration coverage of all seven public declarations;
4. explicit answers to:
   - Is `Iso.refl _` mathematically and definitionally justified?
   - Is homologicality transported with the correct isomorphism orientation?
   - Does the module add any global instance or hidden premise?
   - Is `Exact`, rather than `ShortExact`, the strongest justified statement?
   - Does the monic cokernel comparison have the intended source, target, and
     direction?
   - Are the trust/count records exact and non-promotional?
5. commands actually run and their outputs;
6. any residual risk that compilation and the emitter cannot detect.
