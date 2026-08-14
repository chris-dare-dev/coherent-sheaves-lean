# Third-party licences

The repository source is MIT except where an individual file says otherwise.

`BridgelandStabLean/ForMathlib/CategoryTheory/Triangulated/TStructure/ImageFactorisation.lean`
is repository-maintained ForMathlib work derived from Mathlib's abelian-heart
API. It retains the Mathlib contributors' Apache-2.0 header and is covered by
[`Apache-2.0.txt`](Apache-2.0.txt).

Five repository-maintained deformation and topology modules were derived from
`mattrobball/BridgelandStability` at revision
`9e48f23a382ba117b63076a33e0e775389fef1ba` and then adapted to the owner API:

- `BridgelandStabLean/Foundation/Deformation/SeminormComparison.lean`
- `BridgelandStabLean/Foundation/Deformation/LocalInjectivity.lean`
- `BridgelandStabLean/Foundation/Deformation/LocalComparison.lean`
- `BridgelandStabLean/Foundation/Deformation/ConnectedComponent.lean`
- `BridgelandStabLean/Foundation/Deformation/LocalHomeomorphism.lean`

They retain their Mathlib contributors' Apache-2.0 headers and are covered by
[`Apache-2.0.txt`](Apache-2.0.txt) and
[`BridgelandStability-NOTICE.txt`](BridgelandStability-NOTICE.txt). They are
maintained and built as ordinary owner modules: no separately versioned source,
vendor tree, compatibility root, or anchor root remains.
