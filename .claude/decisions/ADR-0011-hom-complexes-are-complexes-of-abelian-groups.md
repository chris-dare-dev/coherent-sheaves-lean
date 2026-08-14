# ADR-0011 — Hom-complexes are complexes of abelian groups; `k`-linearity is a refinement

- **Status:** accepted
- **Date:** 2026-08-13 (UTC)
- **Decider:** Chris Dare
- **Refines:** ADR-0010, which chose a bespoke `DGCategory` structure but left
  open what the Hom-complexes are complexes *of*.
- **Related:** chris-dare-dev/derived-alg-geo-lean#335 (the epic this landed
  in), #337 (where the question was first surfaced)

## Context

ADR-0010 settled the encoding — a bespoke structure rather than an enriched
category — because at the pin `CochainComplex (ModuleCat k) ℤ` is not monoidal.
It did not settle the codomain of `dgHom`, and the first draft took the obvious
choice: `CochainComplex (ModuleCat k) ℤ`, so that the dg category is `k`-linear
by construction.

That choice collided with the environment three times, in three different
places, in the space of one epic:

1. **The `C^dg` mismatch.** Mathlib's `CochainComplex.HomComplex F G` lands in
   `CochainComplex AddCommGrpCat ℤ`, not in `ModuleCat k`. The whole point of
   `dg-enhancements-e4` is to build `C^dg` from `HomComplex`, and the types do
   not line up. The `k`-linear content is present one level down
   (`Cochain.δ_hom` is `R`-linear when the base category is `R`-linear), but
   the packaged complex is not.
2. **Carrier opacity in the non-vacuous instance.** `ModuleCat.of k k`'s carrier
   is not transparent to instance search, so goals stated on
   `↑((dgHom X Y).X p)` could not use `mul_assoc` or `zero_mul`. Two workarounds
   were needed and documented.
3. **The product dg category.** The same opacity blocked `LinearMap.mk₂`'s
   bilinearity obligations outright: the goal is not recognised as living in a
   product type, and neither workaround from (2) applies to `mk₂`'s obligations.
   The product's `DGCategoryStruct` instance could not be built at all.

Three collisions with one cause is a design signal, not three accidents.

## Decision

**`dgHom : C → C → CochainComplex AddCommGrpCat ℤ`.** A dg category is
ℤ-linear by definition. `k`-linearity is a separate class, `DGLinear k C`,
carrying `k`-linearity of the differential and of the composition in each
argument, over module structures supplied as a parameter.

This mirrors how Mathlib layers `CategoryTheory.Linear` over `Preadditive`
rather than baking a ring into the base definition.

`DGCategoryStruct` and `DGCategory` consequently have **no `k` parameter at
all**, which removed the `dgHom (k := k)` pinning that every field type in the
first draft needed.

## Consequences

- `dg-enhancements-e4` can hand `CochainComplex.HomComplex` to `dgHom`
  directly. The mismatch in #337 dissolves rather than being worked around.
- The three-way friction above disappears at its source rather than acquiring
  three separate workarounds.
- A `k`-linear statement now requires an explicit `[DGLinear k C]`. That is the
  intended cost: linearity is a hypothesis where it is used, not a global
  assumption.
- The module structures in `DGLinear` are a **class parameter**, not a field. A
  field cannot serve as an instance inside the same class's later field types;
  the version that tried produced a stuck `HSMul` metavariable on the first
  axiom.
- Carrier opacity is not gone — `AddCommGrpCat.of` is as opaque as
  `ModuleCat.of` — but it now bites only where an actual ring structure is
  needed, which is the non-vacuous example, and the idiom for that is recorded
  in `DGLean/Category/Instances.lean`.

## What this does not decide

The product dg category's `DGCategoryStruct` instance is still not built. The
recommended construction — from Mathlib's biproduct API on `HomologicalComplex`
rather than a hand-rolled `of (_ × _)` — is unchanged by this ADR and is
recorded in `DGLean/Category/Product.lean`.
