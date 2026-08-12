# Issue #83 adversarial review — abstract stability-in-families interfaces

Date: 2026-08-11
Branch: `agent/issue-83-families-interfaces`
Base: issue #82 head / merged PR #138 lineage
Verdict requested: adversarial source/API review; no promotion is requested

## What the source says at the pinned coordinates

Checked against the repository-pinned v4 PDF on 2026-08-11:

- p. 94, Definition 20.5(1): central charge is universally locally constant;
- p. 94, Definition 20.5(2): geometric stability is universally open;
- p. 94, Definition 20.5(3): integration to an HN structure is required
  after every essentially-finite-type Dedekind base change;
- p. 95, weak clause (0): the charge is defined over `Q[i]` and the
  zero-charge torsion subcategory is noetherian;
- p. 95, weak clause (2'): generic openness of semistability;
- p. 95, weak clause (3'): an induced weak HN structure together with a
  noetherian zero-charge torsion subcategory;
- p. 102, Definition 21.15(4): one quadratic form on the real quotient is
  negative on the descended charge kernel and nonnegative on every fiber
  semistable class;
- p. 102, Definition 21.15(5): boundedness;
- pp. 106–107, Theorem 22.2: the complex-manifold/local-isomorphism result;
  its proof invokes Definition 20.5(2)–(3) and Definition 21.15(4)–(5).

This packet paraphrases the clauses and does not supply a new source quote.
The declarations now have candidate source-coordinate links, but governance
keeps the registry coordinate at `target` pending adversarial review and owner
acceptance. A later `mapped` status would still record only a candidate
mapping, not a source-faithfulness verdict.

## Files and claims

### `StabilityCondition/Families/Basic.lean`

- `ChargeProbe` packages a caller-supplied point type, topology, and charge
  function. `UniversallyLocallyConstantCharge` uses Mathlib's actual
  `IsLocallyConstant` under an outer universal probe quantifier.
- `OpenLocusProbe` and `UniversalOpenness` use Mathlib's actual `IsOpen`.
- `GenericSemistabilityProbe.IsGenericallyOpen` says that semistability at the
  designated generic point extends to an open neighbourhood.
- `DedekindHNProblem` makes the eligible-base-change predicate and the HN
  witness type explicit. `IntegratesAfterDedekindBaseChange` requires a
  witness for every eligible test.
- `WeakDedekindHNProblem` adds the noetherian zero-charge obligation to the
  same base-change quantifier.
- `BoundednessProblem` makes every numerical moduli problem and its geometric
  boundedness predicate caller data; `UniversalBoundedness` merely quantifies
  it.
- `OrdinaryDefinition20_5Conditions` and
  `WeakDefinition20_5Conditions` expose their source clauses as separate
  projections.

### `StabilityCondition/Families/Ordinary.lean`

- `OrdinaryStabilityInFamiliesData` is the top-level ordinary five-condition
  package: Definition 20.5(1)–(3), genuine quotient-uniform support for
  Definition 21.15(4), and the explicit boundedness predicate for clause (5).
- `OrdinaryStabilityInFamiliesData.punit` is an inhabited constant-family
  witness. Every universal index is `PUnit`; it still requires a genuine
  single-locus quadratic-support input.

### `StabilityCondition/Families/Weak.lean`

- `HasGaussianRationalValues` is only the pointwise coefficient presentation
  `z = p + q*i` for rational `p,q`. It is applied to the actual additive map
  `W.Z`; it does not define a bundled Gaussian-rational subring.
- `WeakChargeProbe.toChargeProbe` derives values from the actual fiber
  function and actual `K₀ C` class, preventing an unrelated charge probe.
- `WeakSemistabilityProbe.toGenericProbe` derives its locus from the actual
  `WeakStabilityFunction.IsSemistable` predicate.
- `WeakDefinition20_5ClauseZero` combines the rational-coefficient charge
  condition with the repository's actual
  `IsNoetherianTorsionSubcategory` predicate on each zero-charge class.
- `WeakQuotientQuadraticSupportData` is the one-fiber input used to construct
  the existing `QuotientUniformQuadraticSupportData` for a constant family.
- `WeakStabilityInFamiliesData` packages clauses (0), (1), (2'), (3'), (4),
  and (5). The support field is the genuine issue-#82 quotient package.
- `WeakStabilityInFamiliesData.punit` has inhabited `PUnit` indices
  everywhere, so no universal clause is proved by an empty index type.

### `StabilityCondition/Families/Theorem22.lean`

- `Theorem22_2SourceClauses` contains exactly openness, Dedekind HN
  integration, uniform quotient support, and boundedness.
- `Theorem22_2DependencyContract` adds explicit premises for relative-category
  base change, semiorthogonal base change, relative HN geometry, moduli
  geometry, and complex-analytic deformation theory.
- There is deliberately no declaration deriving a complex manifold or local
  isomorphism from the contract.

## Explicit boundaries and nonclaims

1. The weak adapter has one fixed category and one fixed heart. It is not a
   family of categories `D_s`.
2. No type in this change represents a scheme, Dedekind scheme, morphism of
   schemes, perfect object, relative heart, or base-change functor.
3. `DedekindHNProblem.IsEligible` is caller data. The library does not prove
   that any morphism is essentially of finite type or Dedekind.
4. HN witness types are interfaces. No relative HN structure is constructed.
5. `BoundednessProblem.IsBounded` is caller data. No moduli functor, stack,
   bounded family, or finite-type parameter space is constructed.
6. Constant `PUnit` witnesses prove logical nonvacuity only. They do not model
   a nontrivial geometric family.
7. Sections 22–23 are not formalized. Theorem 22.2 has a dependency ledger but
   no theorem, and no later induction/deformation theorem is declared.
8. The coverage coordinate remains `target`; compilation is not a
   source-faithfulness verdict or owner signoff.

## Adversarial questions

1. Does the local-neighbourhood formulation of weak generic openness match
   Definition 20.5(2') exactly enough for an interface, or does the source
   require an additional curve/base-change hypothesis that should appear as
   another field on the probe?
2. Does the outer probe quantifier honestly represent every base change and
   relative object, or should a future geometric package replace it with a
   dependent base-change/object type before the coordinate can become
   `mapped`?
3. Is the `Q[i]` coefficient predicate correctly oriented, given that it is
   bound to an additive `W.Z` but does not package an explicit factorization
   through a Gaussian-rational additive group?
4. Does weak clause (3') need more compatibility between the HN witness and
   the noetherian predicate than their conjunction currently records?
5. Is the ordinary package's generic semistable-class locus sufficient as an
   abstract input to clause (4), while explicitly not pretending those
   classes come from geometric fibers?
6. Does `Theorem22_2DependencyContract` omit any prerequisite used between
   the four cited source clauses and the complex-analytic conclusion?
7. Do any names or docstrings imply schemes, moduli boundedness, or Theorem
   22.2 itself has been proved?

## Validation checklist

Run from the worktree root:

```sh
lake build
lake exe runLinter BridgelandStabLean
lake env lean scripts/Audit.lean 2>&1 | python3 scripts/check_audit.py
lake env lean scripts/Census.lean
python3 scripts/check_coverage_map.py
git diff --check
rg -n '\b(sorry|admit|axiom)\b' BridgelandStabLean/StabilityCondition/Families
```

Expected census after this change:

- 116 modules;
- 1621 authored declarations;
- 114 private declarations, 100 of them theorems;
- 154 structure projections;
- 1353 hand-audited public declarations;
- 943 gated theorems, 40 gated structures, 370 other gated declarations;
- zero public non-projection declarations outside the hand audit.
