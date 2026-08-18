/-
Axiom audit. First build the optional specialization and development modules listed in
`README.md`, then run: `lake env lean scripts/AlgebraicGeometryAudit.lean`.

Every line must print either "does not depend on any axioms" or exactly
`[propext, Classical.choice, Quot.sound]`. Any occurrence of `sorryAx` is a
failure: this library has no `sorry`, and the trust boundary is carried by the
*fields* of `NumericalVariety`, which are visible in its type, not by holes.

Since #480 the records live in the per-area submodules under
`scripts/AlgebraicGeometryAudit/`; this file is the imports-only umbrella that
makes `lake build AlgebraicGeometryAudit` elaborate every record. `#print
axioms` output does NOT replay across the import boundary, so the
gates run each area file directly; adding a declaration means adding
it to the area file its module belongs to.
-/

import AlgebraicGeometryAudit.Core
import AlgebraicGeometryAudit.GeometricLedgers
import AlgebraicGeometryAudit.Moduli
import AlgebraicGeometryAudit.Projective
import AlgebraicGeometryAudit.SchemeDerived
import AlgebraicGeometryAudit.StabilityConditionFamilies
