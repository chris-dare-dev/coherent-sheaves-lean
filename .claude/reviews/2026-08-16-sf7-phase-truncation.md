# SF7.1 finite phase-truncation review

Date: 2026-08-16
Reviewer: Codex engineering review
Source: arXiv:2607.28411v1, Corollary A.23

## Claim level

This is an engineering review of the formal phase-truncation argument against
the pinned source. It does not promote Appendix A to `reviewed` or
`formalized`: Theorem A.17's compact-generation and Ind-extension proof is a
separate SF7 deliverable.

## Source argument

The proof of Corollary A.23 applies Theorem A.17 at every phase and obtains
the two recognition formulas (A.8). For an object whose image has target HN
phases `phi_1 > ... > phi_m`, it truncates at `phi_1`. Formula (A.8) puts the
first and third terms in the weak lower and strict upper target phase cuts;
the first image is therefore semistable of phase `phi_1`. Repeating the
construction terminates after finitely many target phases.

## Formal realization

- `HNFiltration.exists_headTailFiltration` makes the finite decrease explicit:
  the target tail has length `n - 1`, and its phase `j` is original phase
  `j + 1`.
- `InducedTStructures.isZero_of_map_isZero` handles the zero-length case from
  formula (A.8), without adding conservativity as an extra bounded axiom.
- At the top target phase, the mapped canonical source truncation triangle and
  the target head/tail triangle have the same t-structure halves. Mathlib's
  truncation-triangle uniqueness identifies their head and tail objects.
- `InducedTStructures.hn_exists` recurses on the target tail and assembles the
  source triangle while retaining a strict phase window. The decreasing target
  HN length is the termination measure.
- `InducedTStructures.preimageData` combines this HN theorem with the previously
  proved Hom-vanishing theorem.

No presentability, coproduct, compact-generation, Ind-extension, or geometric
scheme hypothesis is inferred here. Those hypotheses are responsible for
constructing `InducedTStructures` and remain assigned to #477 and #476.
