# SF7.2 compactness correction review

## Finding

The first compact-generation substrate encoded `IsCompactObject K` by asking
the ordinary set-valued coyoneda functor `Hom(K, -)` to preserve coproducts.
The target coproduct was therefore a disjoint union of Hom sets. That is not
the triangulated definition, whose target is the direct sum of additive Hom
groups.

## Correction

- `IsCompactObject` now uses `preadditiveCoyoneda.obj (op K)`.
- `IsCompactObject.coproductComparisonIso` exposes the defining direct-sum
  comparison.
- `map_ι_coproductComparisonIso_hom` proves compatibility with each coproduct
  injection.
- Left-adjoint preservation of compact objects is rebuilt using
  `Adjunction.homAddEquiv`, so the comparison remains additive.

## Boundary

This correction is required before proving compact-source Hom control for a
mapping telescope. It does not itself assert the telescope/direct-limit
formula or Brown representability.
