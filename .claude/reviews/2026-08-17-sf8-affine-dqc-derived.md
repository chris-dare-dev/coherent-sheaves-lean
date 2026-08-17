# SF8.0 affine `Dqc` derived substrate review

Date: 2026-08-17

Issue boundary: the first supported layer of #528. This change does not close
the general-scheme issue.

## Implemented boundary

- `AffineQuasicoherentSheaves R` is the actual full category of
  quasi-coherent module sheaves on `Spec R`.
- Finite products and the abelian structure are transported across Mathlib's
  proved tilde equivalence with `ModuleCat R`; the all-sheaf category is not
  relabelled as quasi-coherent.
- `AffineQuasicoherentDerivedCategory R` is the derived category of that
  genuine abelian category. Its triangulated structure is Mathlib's derived
  structure, not an independent axiom or user-selected switch.
- The tilde and global-sections sides of the affine equivalence induce actual
  triangulated derived functors.
- Both derived functors have concrete, degreewise cohomology-comparison
  isomorphisms.

## Remaining #528 boundary

- Mathlib does not yet prove that quasi-coherent sheaves on every scheme form
  an abelian category.
- The unbounded essential-surjectivity theorem identifying the affine derived
  quasi-coherent category with the quasi-coherent-cohomology locus inside the
  derived category of all sheaves is not claimed here.
- Consequently this change does not assert the general-scheme inherited
  coproduct structure, the bounded-coherent equivalence, compact equals
  perfect, the compact-generator closure, or `S`-linear compatibility.
- The derived tilde and Gamma functors are not named an equivalence until their
  localization-level unit and counit are constructed.
