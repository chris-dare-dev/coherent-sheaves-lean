# Stability-foundation ownership record

This file is retained at its historical path because several source modules
link here for design context. It no longer describes a live dependency API.

The initial port used the `mattrobball/BridgelandStability` source as a
comparison oracle. Literal source independence was completed on 2026-08-14:

- the entire vendored source tree was deleted;
- the external compatibility and t-structure anchor roots were deleted;
- the two exact Apache-2.0 helper copies were replaced by owner-native proofs;
- the five retained Apache-2.0 deformation/topology implementations were
  adapted into owner namespaces and imports, with provenance recorded under
  `LICENSES/`;
- every phase, symmetry, metric, mass, weak-stability, and tilting consumer now
  reaches repository-owned declarations;
- deformation now constructs global HN filtrations, the deformed slicing, its
  local finiteness, the resulting stability condition, and a quantitative
  slicing-distance bound inside `BridgelandStabLean.Foundation`;
- CI has a zero-import gate with no allowlist for the retired module roots.

The canonical modules are:

| Concern | Owner module |
|---|---|
| Postnikov towers and HN filtrations | `BridgelandStabLean.Foundation.PostnikovTower`, `HNFiltration` |
| Slicings and phase truncation | `BridgelandStabLean.Foundation.Slicing` |
| Grothendieck group and class maps | `BridgelandStabLean.Foundation.TriangulatedGrothendieck` |
| Stability functions and abelian HN theory | `BridgelandStabLean.Foundation.StabilityFunction` |
| Stability conditions and topology | `BridgelandStabLean.Foundation.StabilityCondition`, `Deformation.StabilityTopology` |
| Deformation theorem | `BridgelandStabLean.Foundation.Deformation.Theorem` |
| Local comparison and injectivity | `BridgelandStabLean.Foundation.Deformation.LocalComparison`, `LocalInjectivity` |
| Component local-homeomorphism theorem | `BridgelandStabLean.Foundation.Deformation.LocalHomeomorphism` |
| T-structure heart bridge | `BridgelandStabLean.TStructureHeartBridge` |

Historical API reconnaissance below this point was deleted with the source it
described. Git history remains the authoritative provenance record.
