# The dg surface of the pinned Mathlib — measured, 2026-08-13 (UTC)

For `dg-enhancements-e1` (chris-dare-dev/derived-alg-geo-lean#329). This note
answers ADR-0010's Question 1 with evidence rather than estimate.

**Environment.** Every command below was run against
`mathlib_rev = 520045ab14e26149ee970e2e617ca04b09bde5d6` from `pins.json`,
toolchain `leanprover/lean4:v4.32.1`, in a detached worktree of that revision.
Elaboration probes ran with `lake env lean` in a checkout whose
`.lake/packages/mathlib` is at that same revision and is fully built. No probe
file is merged.

## Summary

| Question | Answer at the pin |
|---|---|
| Does Mathlib have a dg category, dg functor, or quasi-equivalence? | **No.** Zero matches, repository-wide. |
| Is `CochainComplex (ModuleCat k) ℤ` monoidal? | **No.** `HasTensor` does not synthesize. This is the load-bearing failure. |
| Is `ChainComplex (ModuleCat k) ℕ` monoidal? | **Yes.** |
| Is the Hom cochain complex present? | **Yes**, with `Cochain`, `δ`, `Cocycle`, and composition. |
| Is Hⁿ(Hom•(K,L)) ≅ Hom_{K(C)}(K, L⟦n⟧) proved? | **Yes**, as an `AddEquiv`. |

The headline: the H⁰ seam is in better shape than the roadmap assumed, and the
enriched encoding is in worse shape.

## 1. The negative result — no dg anything

```
$ grep -rlE "DifferentialGraded|DGCategory|DgCategory|QuasiEquivalence|quasiEquivalence" Mathlib --include='*.lean'
(no matches)
```

Repository-wide, at the pin. The track's subject is genuinely absent, which is
what makes it a track rather than a wrapper.

## 2. The enriched route does not close at the pin

`EnrichedOrdinaryCategory` exists and has exactly the shape a dg category needs
(`Mathlib/CategoryTheory/Enriched/Ordinary/Basic.lean:43`): an `EnrichedCategory V C`
plus `homEquiv : (X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y))` and its unit/composition
coherences.

The enriching category is the problem. `Mathlib/Algebra/Homology/Monoidal.lean:335`
gives `MonoidalCategory (HomologicalComplex C c)`, and the shape instance
`TensorSigns (ComplexShape.up ℤ)` exists
(`Mathlib/Algebra/Homology/ComplexShapeSigns.lean:181`). But the probes fail:

```lean
-- FAILS: failed to synthesize  HomologicalComplex.HasTensor K L
example (k : Type) [CommRing k] (K L : CochainComplex (ModuleCat k) ℤ) :
    HomologicalComplex.HasTensor K L := inferInstance

-- FAILS: failed to synthesize  MonoidalCategory (CochainComplex (ModuleCat k) ℤ)
noncomputable example (k : Type) [CommRing k] :
    MonoidalCategory (CochainComplex (ModuleCat k) ℤ) := inferInstance
```

while every ingredient individually succeeds — `TensorSigns (ComplexShape.up ℤ)`,
`MonoidalCategory (ModuleCat k)`, `Preadditive`, `HasZeroObject`,
`HasFiniteCoproducts` — and the ℕ-indexed case succeeds outright:

```lean
-- SUCCEEDS
noncomputable example (k : Type) [CommRing k] :
    MonoidalCategory (ChainComplex (ModuleCat k) ℕ) := inferInstance
```

**Diagnosis.** The degree-`n` component of a tensor product is a coproduct over
`{(i,j) : i + j = n}`. For `ComplexShape.up ℤ` that index set is infinite; for
`ChainComplex _ ℕ` it is finite. Mathlib's instances supply the finite case —
the `example` closing `Monoidal.lean` advertises exactly
`HasFiniteCoproducts` + `PreservesFiniteCoproducts` and concludes
`MonoidalCategory (ChainComplex D ℕ)`. Nothing supplies the ℤ case.

This is an **instance and API gap, not a mathematical obstruction**:
`ModuleCat k` has all small coproducts and tensoring preserves them, so the
required `HasTensor`/`HasGoodTensor₁₂`/`HasGoodTensor₂₃` instances are
constructible. They are simply not constructed at the pin, by anyone.

An honest correction: the first probe round appeared to show a deeper failure,
but that round was missing `import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic`,
so `MonoidalCategory (ModuleCat k)` itself failed. With the import added, the
failure localizes precisely to `HasTensor` on the ℤ-indexed shape. The bad
probe is recorded here rather than deleted.

## 3. The Hom complex is there, and so is most of the seam

`Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean` provides, at the pin:

- `Cochain F G n` (`:68`) with `mk`, `v`, `ofHom`, `ofHoms`, `ofHomotopy`
- `Cochain.comp` (`:220`) — the graded composition law, with its degree equation
  carried explicitly
- `δ` (`:402`) and `δ_hom` as an `R`-linear map (`:433`)
- **`CochainComplex.HomComplex F G : CochainComplex AddCommGrpCat ℤ`** (`:567`)
- `Cocycle F G n` (`:580`), `Cocycle.equivHom : (F ⟶ G) ≃+ Cocycle F G 0` (`:687`)
- `Cochain.equivHomotopy` (`:786`), `Cochain.single`, and functorial `map`

and `HomComplexCohomology.lean` provides `CohomologyClass K L n` together with

```lean
noncomputable def CohomologyClass.homAddEquiv :
    CohomologyClass K L n ≃+
      ((HomotopyCategory.quotient C _).obj K ⟶ (HomotopyCategory.quotient C _).obj (L⟦n⟧))
```

That is **Hⁿ(Hom•(K,L)) ≅ Hom_{K(C)}(K, L⟦n⟧)** — the H⁰ seam, proved, at the
hom-set level. All three P6 probes elaborate clean.

**Consequence for DG1.** `dg-enhancements-e4`'s headline
(`H⁰(C^dg A) ≌ HomotopyCategory A`) is not a from-scratch construction. The
mathematical content is present; what is missing is the categorical packaging —
functoriality of the equivalence in both variables and compatibility with
composition — so that hom-set bijections assemble into an equivalence of
categories. The roadmap's `size: L` for e4 should be revisited downward, and
`size` for e2 upward if Option B is chosen.

## 4. What this does to ADR-0010

Option A (enrich over cochain complexes) cannot be taken as written: its
enriching category does not exist at the pin. Three routes remain, and the
decision is now between them rather than between the original two. See the ADR.

## Commands

```sh
git -C <mathlib> worktree add --detach /private/tmp/mathlib-pin-520045ab 520045ab14e2...
grep -rlE "DifferentialGraded|DGCategory|DgCategory|QuasiEquivalence|quasiEquivalence" Mathlib --include='*.lean'
grep -rn "TensorSigns" Mathlib --include='*.lean' | grep -E "instance|structure|def "
grep -nE "^(def|structure|abbrev|noncomputable def|theorem) " Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean
cd <checkout-at-pin> && lake env lean DgProbe.lean     # round 1, bad imports
cd <checkout-at-pin> && lake env lean DgProbe2.lean    # round 2, localized failure
```

The probe files are throwaway and unmerged, per the epic's scope.
