# SF7.2 mapping-telescope foundation review

## Scope

This slice implements the first missing categorical primitive for the honest
Brown construction in Theorem A.13 of arXiv:2607.28411v1.

- `MappingTelescope.shiftMap` sends each countable-coproduct summand along the
  transition map into the next summand.
- `MappingTelescope.map` is `1 - shift`.
- `MappingTelescope.Data` presents a telescope as a distinguished cone of that
  map, and `chosen` constructs one from the pretriangulated axiom.
- `Data.exists_desc` and `Data.exists_desc_comp_ι` use triangle exactness to
  factor every compatible family of maps through the telescope.

## Trust boundary

The construction assumes only the existing countable coproduct and
pretriangulated structures. It introduces no proposition saying that compact
generators automatically yield approximation maps, and it does not claim a
compact-source Hom equivalence for telescopes.

The remaining Brown work is to build the successive approximation tower and
prove the compact-source Hom computation that gives the surjectivity and
shifted injectivity fields of `TStructure.ApproximationMap`. The geometric A.14
restriction equivalences remain a separate obligation after that.
