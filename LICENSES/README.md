# Third-party licences

The owner-authored repository trunk is **MIT**; see [`LICENSE`](../LICENSE).
The following retained third-party material is Apache-2.0 and is not
relicensed by the repository-level MIT licence.

## Vendored BridgelandStability foundation

`vendor/BridgelandStability/` contains the 68-module reachable source surface
ported from
[`mattrobball/BridgelandStability`](https://github.com/mattrobball/BridgelandStability)
at upstream revision `9e48f23a382ba117b63076a33e0e775389fef1ba`.
The retained source headers, the component-local `LICENSE`, and its `NOTICE`
record the origin and the v4.32.1 port modifications.

## Compatibility files derived from the same foundation

Two files below
`BridgelandStabLean/ForMathlib/CategoryTheory/` contain material previously
vendored from the same Apache-2.0 source:

| file | vendored from |
|---|---|
| `ObjectProperty/FullSubcategory.lean` | `BridgelandStability/HeartEquivalence/Basic.lean` |
| `Triangulated/TStructure/HeartAbelian.lean` | `BridgelandStability/TStructure/HeartAbelian.lean` and `HeartEquivalence` modules |

They retain their Apache-2.0 headers. The repository-wide copy of the licence
is [`Apache-2.0.txt`](Apache-2.0.txt), as Apache-2.0 §4(a) requires.

Apache-2.0 material may be redistributed inside this MIT-licensed repository
provided its notices survive. It may become MIT only through an independent
re-proof or an explicit dual-licence grant; a header-only rewrite is not a
relicensing mechanism.
