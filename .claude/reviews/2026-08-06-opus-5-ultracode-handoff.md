# Opus 5 UltraCode review handoff — 2026-08-06 Lean work

Status: **READY FOR INDEPENDENT REVIEW**

This is a review brief, not a review verdict. It does not alter
`formalization.yaml`'s `human_review: none`, and an AI review must not be
recorded as human source-faithfulness review.

## Pinned state and scope

- Repository: `chris-dare-dev/bridgeland-stab-lean`
- Branch to review: `main`
- Theorem baseline: `56c7531c4e47d2c067e6158925d5dfc0539967e7`
- Pre-session baseline: `b4cbf478b80c14116f4f81b9fe80bcc5dea5c73e`
- PR #66 merge: `326d72b8ec4d4fde54362d91e2e9f9f851f56611`
- PR #67 merge: `56c7531c4e47d2c067e6158925d5dfc0539967e7`
- Review delta: 39 files, 7,655 insertions, 292 deletions
- Toolchain: Lean `v4.29.0`
- Anchor: `mattrobball/BridgelandStability@9e48f23a382ba117b63076a33e0e775389fef1ba`
- Transitive Mathlib: `8a178386ffc0f5fef0b77738bb5449d50efeea95`

The commit containing this handoff is documentation-only relative to the
theorem baseline. Review every file in the delta, but treat `56c7531` as the
immutable state whose Lean claims and verification results are being audited.

Useful first commands:

```bash
git status --short --branch
git rev-parse HEAD
git diff --stat b4cbf478b80c14116f4f81b9fe80bcc5dea5c73e 56c7531c4e47d2c067e6158925d5dfc0539967e7
git log --reverse --oneline b4cbf478b80c14116f4f81b9fe80bcc5dea5c73e..56c7531c4e47d2c067e6158925d5dfc0539967e7
```

## Review request for Opus 5 UltraCode

Perform an independent theorem, API, instance, and trust-record review of the
entire pinned delta. Read the Lean sources themselves; do not infer correctness
from this summary, successful elaboration, or theorem names.

For every substantive finding:

1. assign P0, P1, P2, or P3 severity;
2. cite the exact file and narrow line range;
3. distinguish a mathematical error, an overly strong or weak statement, an
   instance/API hazard, a proof-maintenance problem, or a trust-record error;
4. explain whether downstream theorems are affected;
5. suggest the smallest defensible correction.

If there are no findings, say so explicitly and list the files and verification
commands actually inspected. Do not return a generic build-success summary.

Do not edit during the first pass. In particular, do not fill any faithfulness
verdict in the existing 2026-08-05 worksheet and do not change
`human_review: none`. Findings from this session are machine review unless a
human separately performs and records the four-axis source review.

## Non-negotiable mathematical boundaries

The review must preserve or challenge these boundaries explicitly:

- `GLTilde.universalCoverData` packages a covering map, surjectivity, and a
  simply connected source. The deck group is supplied separately by
  `exact_deckHom_toMatHom`. The pinned Mathlib has no single bundled predicate
  matching the paper's phrase “universal covering space.”
- `AutPairQuot v` is a quotient of compatible pairs `(Φ, λ)`, not a proved
  identification with the paper's bare `Aut(D)`.
- `(deck 1, [2])` is proved to lie in the combined action kernel. The code does
  not claim that this element generates the full kernel in an arbitrary
  category.
- For a general class map `v`, distance zero reconstructs the observable
  charge `Z.comp v`. Literal equality of `Z` needs `Function.Surjective v`.
  The ordinary `K₀ C` specialization is unconditional because `v = id`.
- The named pseudo/extended metric structures are constructors, not installed
  global instances. Their topology is built with
  `PseudoEMetricSpace.ofEDistOfTopology`, and the `rfl` regression theorems are
  intended to rule out a competing topology or typeclass diamond.
- Proposition 8.1 is not complete. Reverse neighborhood cofinality and the
  compatible metric constructors are conditional on the explicit proposition
  `StabilityMassTriangleInequality`.
- Defining a proposition is not proving it. The audit entry for
  `StabilityMassTriangleInequality` only checks that the definition itself is
  axiom-clean.
- The remaining mass-triangle theorem is mathematically substantive. Ikeda's
  proof of even the `t = 0` case uses HN polygons, a short-exact inequality,
  reduction through an HN tower using the octahedral axiom, and heart
  cohomology. It must not be replaced by an unproved assumption or an
  accidentally stronger categorical lemma.

## Commit chain to audit

| Commit | Intended milestone |
|---|---|
| `d997e42` | universal cover, topological and effective symmetry chain |
| `484821a` | merge of current `main` into the PR #66 branch |
| `326d72b` | merge of PR #66 |
| `e22a10b` | full stability distance and full autoequivalence isometry |
| `d6094d0` | uniqueness and finiteness of HN mass |
| `bfd0786` | identity of indiscernibles / separation |
| `160f0f3` | Proposition 8.1 topology infrastructure and named metric constructors |
| `56c7531` | merge of PR #67 |

Review the merge topology as well as the final tree. The PR #66 branch merged
`main` before landing; check that no declarations were silently replaced or
that imports did not resolve to unintended instances after the merge.

## Lean review map — topology and universal cover

### `BridgelandStabLean/GroupAction/GLTildeTopology.lean`

Purpose: global coordinates
`ℝ × (0,∞) × ℝ × (0,∞)` for `GLTilde`, transported topology, continuous matrix
projection, contractibility, and simple connectedness.

Review closely:

- rotation sign and phase convention in `rotationMatrix`, `phaseTranslation`,
  and `liftedRotation`;
- positivity of both diagonal entries of `alignedMatrix`;
- the noncomputable normalization `upperDeckIndex` / `upperSectionZero`;
- both inverse laws for `glTildeCoordinateEquiv`;
- whether the transported topology is used consistently by all later files;
- whether `ContractibleSpace` genuinely supplies the declared
  `SimplyConnectedSpace` without hidden stronger assumptions.

Key public surface: `glTildeCoordinateEquiv`,
`glTildeCoordinateHomeomorph`, `GLTilde.continuous_toMat`,
`GLTilde.contractibleSpace`, and `GLTilde.simplyConnectedSpace`.

### `BridgelandStabLean/GroupAction/GLTildeCover.lean`

Purpose: coordinates
`S¹ × (0,∞) × ℝ × (0,∞)` for `GL⁺(2,ℝ)`, the product exponential cover in
coordinates, conjugacy with `GLTilde.mat`, and packaged cover data.

Review closely:

- `circleMatrix` orientation and the factor `Real.pi` in `phaseCircle`;
- reconstruction of the second column and determinant positivity;
- `glPosCoordinateHomeomorph` inverse and continuity proofs;
- the general helper `IsCoveringMap.prodMap_id` for missing assumptions or
  excess generality;
- `coordinateProjection_isCoveringMap` and the conjugacy identity
  `glPosOfCoordinates_coordinateProjection`;
- the exact content of `GLTilde.universalCoverData` versus its name and prose.

### `BridgelandStabLean/GroupAction/GLTildeTopologicalGroup.lean`

Purpose: prove the transported topology is compatible with multiplication and
inversion.

Review closely the branch-sensitive phase calculation. The proof relies on
cancellation of the argument term and continuity in the open right half-plane.
Check `coordinateShift`, joint continuity of phase evaluation, explicit inverse
coordinates, and the final `IsTopologicalGroup GLTilde` instance.

### Existing files changed to support the cover

- `GLTilde.lean`: normalized structure/projection changes; ensure the group
  laws and field projections retain their intended definitional behavior.
- `GLTildeFibre.lean`: the kernel is the even phase-deck group, equivalent to
  `Multiplicative ℤ`; recheck the factor of two.
- `GLTildeSurj.lean`: explicit section and projection surjectivity; recheck the
  lift convention against `GLTildeCover.lean`.
- `NormalizedShift.lean`: only deletions in this delta; confirm declarations
  were moved or made redundant rather than accidentally removed from the API.

## Lean review map — topological symmetry actions

### `TopologicalAction.lean`

Purpose: fixed compatible autoequivalence classes act continuously and by
homeomorphisms in the Section 6 topology.

Review the direction of `mapEquiv_phiPlus` / `mapEquiv_phiMinus`, the
`slicingDist_mapEquiv_le` estimate, the seminorm transformation, quotient
descent, and the resulting `ContinuousConstSMul` instance.

### `GLTildeContinuousAction.lean`

Purpose: fixed `GLTilde` elements and fixed product elements act continuously
and by homeomorphisms.

Review uniform phase-relabeling control, the real-linear continuous map
`actCCLM`, condition-number estimates, the orientation of `actC` versus
`actC⁻¹`, and construction of `GLTilde.stabilityHomeomorph`.

### `GLTildeJointContinuousAction.lean`

Purpose: upgrade fixed-element continuity to joint continuity, give
`AutPairQuot v` the discrete topology, and obtain joint continuous actions for
both factors and the product.

Review the compact-window-to-global argument in
`eventually_uniform_shift_displacement`, operator-norm control near the
identity, translation from identity to arbitrary points, and instance
selection. Confirm the discrete topology is a deliberate external design
choice and does not conflict with another topology.

### `CombinedAction.lean`

Purpose: prove the `GLTilde` and `AutPairQuot v` actions commute and install the
direct-product `MulAction`.

Review the contravariant/covariant order in
`gltilde_autPair_smul_comm`, `prod_mk_smul_slicing`, and `prod_mk_smul_Z`.

### `ComponentAction.lean`

Purpose: transport connected-component labels, restrict action maps to
component homeomorphisms, and act by the component stabilizer.

Review quotient well-definedness of `componentSmul`, image equality for
connected components, subtype coercions, and the stabilizer action laws.

### `PeriodMapEquivariance.lean`

Purpose: induced additive equivalences on charge space and equivariance of the
global central-charge map and component local-model chart.

Review inverse laws for all charge equivalences, the order of the two product
actions, and whether `componentLocalModel_chargeMap_equivariant` uses the
correct source and target components.

### `EffectiveAction.lean`

Purpose: triangulated double-shift equivalence, its action on `K₀`, the
deck/double-shift overlap, and the quotient by the full action kernel.

Review all shift signs and coherence isomorphisms, especially
`K₀.mapF_shift_neg_two`, `shiftTwoPair_act_eq_deck_neg_one`, and
`deck_one_shiftTwo_combined_smul`. Confirm faithfulness follows from quotienting
by exactly the kernel of `combinedActionHom`, and that no cyclic-generation
claim leaks into documentation or naming.

### Existing action files changed in the same chain

- `QuotAutAction.lean`: `TriEquiv.inverseIsoOfFunctorIso` derives inverse
  natural isomorphisms from forward ones. Check right-adjoint uniqueness and
  quotient normalization.
- `AutPairAction.lean`: check compatibility datum and product order after the
  quotient normalization.
- `AutStabilityAction.lean`, `SlicingAction.lean`, and `StabilityAction.lean`:
  small bridge/import changes; check for instance ambiguity and accidental
  strengthened assumptions.

## Lean review map — full mass and metric chain

### `StabilityMass.lean`

Purpose: the finite charge-norm sum of an HN filtration and a choice-free
supremum over all HN filtrations, with positivity, isomorphism invariance, and
autoequivalence transport.

Review closely:

- whether zero and nonzero objects are handled without taking `log 0` later;
- the index set and coercions in `HNFiltration.mass`;
- whether the `iSup` envelope is genuinely independent of a non-functorial
  choice;
- transport through inverse and forward functors and all object isomorphisms;
- `ENNReal` finiteness assumptions used downstream.

### `HNMassUniqueness.lean`

Purpose: prove any two HN filtrations of one object have equal mass; identify
the envelope with every finite mass sum and derive finiteness/vanishing.

This is one of the highest-risk proofs. Review the octahedral construction of
the highest-factor/tail triangle, the half-open t-structure at a common leading
phase, induction measure and termination, zero-length/zero-object branches,
and all uses of uniqueness up to isomorphism. Verify that
`HNFiltration.mass_eq_mass` is not circular through `stabilityMass`.

Key downstream facts: `stabilityMass_eq_mass`, `stabilityMass_ne_top`,
`stabilityMass_toReal_eq_sum`, `stabilityMass_eq_zero_iff`, and
`stabilityMass_toReal_pos`.

### `StabilityDistance.lean`

Purpose: an `ℝ≥0∞`-valued distance built from the maximum of `φ⁺`, `φ⁻`, and
ordinary absolute logarithmic mass discrepancy, followed by the supremum over
nonzero objects.

Review totalization of `logMassDist`, the finite branch
`logMassDist_eq_of_ne_top`, symmetry and triangle laws, all `iSup` monotonicity
arguments, exclusion of zero objects, and
`slicingDist_le_stabilityDist`. Ensure no notation can be misread as a product
of stability conditions: juxtaposition occurs only inside scalar mass ratios
or group actions.

### `AutIsometry.lean` and `AutFullIsometry.lean`

Purpose: the former proves exact preservation of the anchor's phase-only
`slicingDist`; the latter proves preservation of all three full-distance
coordinates and the supremal distance.

Review iso-invariance of intrinsic phases, preservation/reflection of zero
objects by an equivalence, pointwise two-sided supremum arguments, quotient
descent, and the functor-object reindexing. Do not silently upgrade the acting
group from `AutPairQuot v` to an external `Aut(D)`.

### `StabilityDistanceSeparation.lean`

Purpose: extract equality of phases and finite masses from zero distance,
reconstruct slicings and observable charges, and prove separation under a
surjective class map.

Review the use of semistable objects to reconstruct charge rays, the zero
object branch, extensionality of slicings and stability conditions, and the
exact placement of `Function.Surjective v`. Check that
`charge_comp_eq_of_stabilityDist_eq_zero` is the strongest unconditional
general statement and that the ordinary specialization uses the identity class
map correctly.

### `StabilityDistanceTopology.lean`

Purpose: analytic comparison of distance balls with the Section 6
`basisNhd`s, plus named compatible pseudo/extended metric constructors.

Review in four layers:

1. full-distance control of phases, mass ratios, and charges;
2. sector estimates for semistable factors, including positivity of cosine
   denominators and strict/non-strict inequality transitions;
3. propagation from factors to arbitrary objects, which must visibly require
   `StabilityMassTriangleInequality` in the reverse direction;
4. neighborhood-basis cofinality and `ofEDistOfTopology` instance design.

Check especially `norm_sum_phaseExp_sub_centralRay_le`,
`cos_mul_stabilityMass_le_norm_charge_of_width`, both primed/unprimed mass
bounds, `exists_basisNhd_subset_stabilityDist_ball`,
`exists_stabilityDist_ball_subset_basisNhd`, and
`stabilityDistanceTopologyCompatible_of_mass_triangle`.

For the typeclass question, verify by inspection and elaboration that:

- there is no global `PseudoEMetricSpace` or `EMetricSpace` instance for the
  stability-condition type;
- `stabilityPseudoEMetricSpace_toTopologicalSpace` and
  `stabilityEMetricSpace_toTopologicalSpace` are definitionally `rfl`;
- `stabilityPseudoEMetricSpace_edist` is definitionally `stabilityDist`;
- locally binding either named structure does not create an instance cycle or
  change the pre-existing Section 6 topology.

### Existing import surface

`BridgelandStabLean.lean` gained imports for all modules above. Check import
order, accidental reliance on transitive imports, and whether importing the
root module creates duplicate or incoherent instances.

## Verification and trust surface

### Verification rerun on merged `main`

The following was observed locally on macOS/aarch64 at theorem baseline
`56c7531` on 2026-08-06:

| Command | Observed result |
|---|---|
| `lake build` | exit 0, 3,780 jobs |
| `lake env lean scripts/Audit.lean` then `python3 scripts/check_audit.py ...` | 497 declarations; allowlist exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx` |
| `lake exe emit --out attest/lean-emission.json` | exit 0; wrote artifact |
| `git diff --exit-code -- attest/lean-emission.json` | exit 0; artifact reproduced byte-for-byte |
| `lake exe lint-style` | exit 0; existing missing `scripts/nolints-style.txt` warning only |
| `lake exe runLinter` | exit 1; exactly six known findings, listed below |
| YAML parse of `formalization.yaml` | valid |
| JSON parse of the attestation and registry | valid |
| `git diff --check` | clean |

Re-run at least the build, strict audit parser, emitter reproducibility check,
and linter. A successful `lake build` alone does not gate `#print axioms` output.

The six declaration-linter findings are the known baseline:

- `StrictAutAction.lean`: missing docstring on `StrictAut.commShift`;
- `StrictAutAction.lean`: impossible-to-infer `ρ` argument on
  `StrictAut.mulActionSlicing`;
- `ComplexBridge.lean`: `actC_one` is not in simp-normal form;
- `AutAction.lean`: unused additive instance on `PostnikovTower.mapF`;
- `AutAction.lean`: unused inverse-additive instance on `Slicing.mapEquiv`;
- `K0Functor.lean`: unused additive instance on
  `isTriangleAdditive_of_isTriangulated`.

None is in `StabilityMass`, `HNMassUniqueness`, `StabilityDistance`,
`StabilityDistanceSeparation`, `StabilityDistanceTopology`, or
`AutFullIsometry`. Confirm this rather than assuming it.

### Trust and provenance files changed today

Review these alongside the Lean sources:

- `formalization.yaml`: theorem boundaries, axiom/build counts, machine-review
  evidence, `known_divergences`, and continued `human_review: none`;
- `registry/bridgeland2007.json`: source records for Definition 1.1,
  Definition 3.3, Lemma 3.4, Definition 5.1, Definition 5.7, Proposition 8.1,
  Lemma 8.2, and the universal-cover obligation;
- `registry/README.md`: registry semantics and unresolved frontier rules;
- `.claude/reviews/2026-08-05-first-faithfulness-review.md`: unfilled human
  worksheet; do not treat it as a completed review;
- `scripts/Audit.lean`: explicit declaration sweep and convention spot checks;
- `scripts/check_audit.py`: parsing/allowlist gate, especially primed names;
- `exe/Emit.lean`: environment-wide axiom emitter configuration;
- `attest/lean-emission.json`: generated environment attestation;
- `lakefile.toml` and `lake-manifest.json`: exact dependency pins, build target,
  audit target, and emitter target;
- `README.md`, `CLAUDE.md`, and `notes/anchor-api-map.md`: public claims and
  implementation notes;
- `.gitignore`: generated/audit-file policy.

The source registry still records unresolved mint-time matching because the
local arXMCP corpus has empty `arxiv_version` values. Do not upgrade a probable
v3 match to a confirmed corpus-version claim. The local corpus size is machine
specific and must not be generalized to the owner's 145-paper personal-PC
corpus.

## Proposition 8.1 exit condition

The next logical chain should be considered safe to start only if this review
finds no defect in the mass definition, HN mass uniqueness, distance
separation, or named metric/topology construction.

Proposition 8.1 becomes complete only after a theorem inhabits:

```lean
CategoryTheory.Triangulated.StabilityMassTriangleInequality
```

without `sorry`, a new axiom, an instance that smuggles in the proposition, or
a stronger assumption disguised as a standard categorical fact. Once that is
proved, the existing conditional chain should yield reverse cofinality,
topology equality, and compatible named metric structures.

The recommended implementation order after review is:

1. heart-level short-exact mass inequality;
2. semistable-left distinguished-triangle reduction via cohomology in the
   heart;
3. arbitrary-left-object reduction along its HN tower using octahedral
   assembly, culminating in `StabilityMassTriangleInequality`.

## Required review deliverable

Return one report with:

- an executive verdict on whether `main@56c7531` is safe as the baseline for
  the mass-triangle chain;
- findings ordered by severity, with exact file/line citations;
- a module-by-module statement/API review covering every Lean file listed
  above;
- an explicit answer on the `PseudoEMetricSpace`/`EMetricSpace` conflict and
  topology-definitional-equality question;
- confirmation or correction of the 497-declaration axiom audit;
- a source-boundary review of Proposition 8.1, Lemma 8.2, the universal-cover
  package, and `AutPairQuot v`;
- recommended fixes separated into blockers, pre-mass-triangle cleanup, and
  optional maintenance;
- a final list of commands actually run and their observed results.

If the review proposes edits, make them only after delivering this first-pass
report so that findings remain reproducible against the pinned theorem state.
