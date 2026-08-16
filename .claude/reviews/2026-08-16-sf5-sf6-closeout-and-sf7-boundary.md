# SF5/SF6 closeout and SF7 theorem-boundary review

Date: 2026-08-16
Reviewer: Codex engineering review
Repository base: `origin/main@0149ef6`

## Scope and claim level

This review checks the open SF5/SF6 issue criteria against declarations that
already exist on `main`, and checks the candidate §3.4 mapping directly
against the pinned arXiv:2607.28411v1 PDF. It is sufficient to propose a
`target -> mapped` registry transition. It is not an independent
source-faithfulness review, owner acceptance, or a `reviewed`/`formalized`
coverage claim.

## SF5 — t-structure calculus

Issue #127 is implemented by the objectwise shift comparisons and their
naturality/triangle compatibility in:

- `TStructure.truncLTShiftIso`, `TStructure.truncGEShiftIso`;
- `TStructure.truncLTShiftNatIso`, `TStructure.truncGEShiftNatIso`,
  `TStructure.truncLEShiftNatIso`, and `TStructure.truncGELEShiftNatIso`;
- `TStructure.originalHeartCohShiftNatIso`;
- `originalHeartCohFunctor_isHomological` and
  `originalHeartCoh_exact_of_distTriang`, both quantified over every integer
  degree;
- `originalHeartCohomologySixTermSequence_exact` and its endpoint results.

Issue #216 is implemented by:

- `TStructure.IsBounded`, `TStructure.IsNondegenerate`, and
  `TStructure.isNondegenerate_of_isBounded`;
- `Functor.IsRightTExact`, `Functor.IsLeftTExact`, and `Functor.IsTExact`,
  including identity, composition, adjunction, and heart-mapping results;
- the all-degree heart cohomology results above; and
- the closed heart-is-abelian prerequisite #213.

The issue text asked for “nondegenerate iff bounded”. That statement is false
without an additional finite-cohomological-amplitude hypothesis. Remark A.3
of arXiv:2607.28411v1 states the correct equivalence: boundedness is
nondegeneracy together with eventual vanishing of the cohomology objects for
each object. The repository correctly proves the unconditional implication
bounded implies nondegenerate and documents why the converse is not claimed.

## SF6 — slicing order and transfer

Issue #211 is implemented by:

- `Slicing.Precedes` and `Slicing.PrecedesWeak`;
- the upper-, lower-, and two-extreme-phase characterizations in
  `Phase/Order/Characterizations.lean`;
- strict, weak, and mixed transitivity, weak reflexivity, and
  `Slicing.precedes_phaseShift_one`;
- `TriEquiv`, `AutQuot`, and `AutPairQuot` equivariance;
- `HasBayerProperty`, `BayerProperty`, their phase characterizations, and
  conjugation invariance; and
- `CofiltrationData`, `CofiltrationProperty`, and
  `CofiltrationPropertyInfinity`.

Issue #215 is implemented by:

- the raw `Slicing.preimagePhase` collection and honest
  `Slicing.PreimageData` constructor boundary;
- identity, composition, natural-isomorphism, equivalence, faithful-functor,
  and phase-shift transport;
- reflected `phiPlus`/`phiMinus`, strict/weak phase windows, order transport,
  and equivariance; and
- an explicit, deliberately uninhabited Appendix-A boundary rather than an
  assertion that a conservative adjoint functor automatically induces a
  slicing.

## Direct v1 source check for §3.4

The pinned PDF (SHA-256
`f8770154235fe2c82698513b4633b3ee509fa11f722190a4c9f573fca589a98c`)
was checked directly on 2026-08-16:

- Definition 3.12 gives exactly the strict inclusion
  `P1(phi) subset P2(< phi)` and weak inclusion
  `P1(phi) subset P2(<= phi)`.
- Lemma 3.13 gives the upper-semistable, lower-semistable, and paired
  extreme-phase characterizations represented by the four `iff` theorems.
- Remark 3.14 gives transitivity and equivariance; its geometric
  pullback/pushforward clause remains conditional in the abstract API.
- Definition 3.16 has the Bayer-property quantifier order represented by the
  abstract autoequivalence-and-shift package.
- Definition 3.22 is the geometric cofiltration property. The repository maps
  only its categorical filtration shape; Propositions 3.21 and 3.24–3.27 are
  not claimed by these abstract declarations.

Accordingly, §3.4 may be marked `mapped`, never `reviewed` or `formalized`,
with the declaration list and limitations recorded in the coverage entry.

## SF7 correction

Theorem A.17 and Corollary A.23 require substantially more than the old
bounded `LeftAdjointInducingPremise`: unbounded `Dqc` categories, coproduct
preservation, a left adjoint, bounded-object detection, conservativity on
bounded objects, S-linearity, and right t-exactness for an Ind-extended
t-structure. Formula (A.8) then produces a phase-indexed family of source
t-structures before the source HN filtration is constructed.

`Slicing.InducedTStructures` now records exactly that bounded intermediate
output, and `Slicing.InducedTStructures.hom_vanishing` proves the first
non-formal preimage-slicing axiom from t-structure orthogonality. The finite
phase-truncation/HN theorem and the large-category construction remain the
explicit next SF7 tasks.
