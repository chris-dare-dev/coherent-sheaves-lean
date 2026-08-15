# SF1 source-faithfulness closeout

Date: 2026-08-14

Source: arXiv:1902.08184v4, pinned by
`registry/coverage-1902.08184v4.json`

Scope: Definition 14.1 through Lemma 14.17, with particular attention to
display (14.1), Definition 14.12, Proposition 14.16, and Lemma 14.17.

## Verdict

**DO NOT PROMOTE.** The current declarations are a sound mapped foundation,
but the source-facing biconditional for Lemma 14.17 is stronger than the
printed statement. Issue #208 and epic #192 must remain open.

This verdict is about source fidelity, not Lean soundness. The relevant
declarations compile, are covered by the stability-condition axiom audit, and
do not introduce a hidden geometric premise.

## Findings

### Definitions 14.1--14.3

`WeakPreStabilityCondition`, `WeakStabilityFunction`, and `zeroCharge` match
the weak ray, heart-valued charge, and zero-charge subcategory used by the
paper. The ordinary-to-weak adapter preserves the slicing and charge
definitionally. These remain appropriate mapped candidates.

### Definition 14.6 and the termination layer

`IsNoetherianTorsionSubcategory` exposes the paper's torsion-class and
noetherianity data. `Weak/Heart/Noetherian.lean` deliberately records that
the literal statements of Lemmas 14.8 and 14.11 remain undeclared; downstream
arguments use the exact chain-termination hypotheses they consume. This is an
explicit nonclaim, not a proof hole.

### Display (14.1)

The strict and weak cutoff conventions agree with the pinned source:
`slopeTors b` uses `b < muMinus`, while `slopeFree b` uses `muPlus <= b`.
`slopeTilt_heart_iff` identifies the resulting HRS heart with extensions of
the torsion class by the shifted torsion-free class.

### Definition 14.12 and Proposition 14.16

`TiltingProperty` records the noetherian zero-charge torsion class and the
tilting envelope with the required Hom vanishing. The phase-language finite
maximum slope is connected to the finite source slope by the source adapter.

`sourceTilt_multiplier` has the correct normalization: the source charge is
definitionally `Z / (I - b)` and is a positive rescaling of the phase-tilted
charge. `sourceTiltConclusion` packages the resulting weak prestability
condition, support, and noetherian zero-charge torsion conclusion. Its support
hypothesis is explicit because the repository separates weak prestability
from the support property.

### Lemma 14.17

The printed lemma classifies a nonzero-charge tilted-semistable object into
two cases. In the negative-original-imaginary case it gives an extension with
an original semistable object and a zero-charge object; Hom vanishing is then
stated as a subsequent `moreover` conclusion under the paper's refinement
hypothesis.

The Lean predicate `IsPhaseTiltTypeTwo` additionally stores:

1. membership of the original semistable object in the phase-cut free class;
2. the positive-new-imaginary Hom-vanishing implication.

The first field is compatible with the canonical cohomology decomposition of
an object in the tilted heart. The second is used by
`isSemistable_of_isPhaseTiltTypeTwo` to exclude zero-charge subobjects. The
repository proves that implication from semistability in
`hom_eq_zero_of_zeroCharge_to_sourceTiltSemistable`, but it does not prove it
from the printed case-(2) extension data alone.

Therefore
`sourceTiltWeakStabilityFunction_isSemistable_iff_classification` is a
strengthened candidate rather than the literal source biconditional. It must
not support a `reviewed` or `formalized` registry status.

## Required resolution

Issue #208 can close only after one of the following is supplied:

1. a proof that the additional type-two fields follow from the printed
   case-(2) data, followed by a literal source-facing biconditional; or
2. an authoritative source clarification showing that the stronger right-hand
   side is intended.

Until then, `sec-14-weak-stability-tilting` remains `mapped`, issue #192 stays
open, and milestone SF1 is not complete.

## Source pages checked

- PDF page 71: Definitions 14.1--14.6.
- PDF page 73: display (14.1), Definition 14.12, and Proposition 14.16.
- PDF page 74: Lemma 14.17 and the proof of Proposition 14.16.
