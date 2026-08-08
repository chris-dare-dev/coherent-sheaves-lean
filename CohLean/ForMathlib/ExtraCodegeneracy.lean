/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.Opposite

/-!
# The alternating coface complex is the opposite of an alternating face complex

Mathlib develops extra degeneracies, and the homotopy equivalence they induce, on the
**simplicial** side: `SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv` is stated
against `alternatingFaceMapComplex` and lands in `ChainComplex`. Čech cohomology, in
`Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean`, is built from
`alternatingCofaceMapComplex` and is **cosimplicial**. Nothing upstream connects the two, so
no Čech vanishing argument can reach the machinery that would prove it.

This file supplies the connection: for a cosimplicial object `Y` in a preadditive category,

```lean
((alternatingCofaceMapComplex A).obj Y).op ≅ (alternatingFaceMapComplex Aᵒᵖ).obj Y.op
```

Both sides are `Y.obj ⦋n⦌` in degree `n` — that much is `rfl` — and both differentials are
`∑ i, (-1) ^ i • δ i`. What is not `rfl` is that `HomologicalComplex.op` distributes over the
sum and the `zsmul`; that is the content, such as it is, and `op_sum` and `op_zsmul` supply
it.

## Why this is the useful direction

The alternative is to define an extra *co*degeneracy structure on augmented cosimplicial
objects and redo the homotopy from scratch, roughly duplicating
`Mathlib/AlgebraicTopology/ExtraDegeneracy.lean`. With this isomorphism that is unnecessary:
a cosimplicial object in `A` is a simplicial object in `Aᵒᵖ`, the upstream extra-degeneracy
theory applies there verbatim, and the isomorphism carries its conclusion back. In
particular `CategoryTheory.Limits.FormalCoproduct.extraDegeneracyCech` — the Čech object of a
family has an extra degeneracy once the terminal object maps into one of its members — is
already upstream and can be used as it stands.

## Not done here

This is one link of the chain in issue #62, not the whole of it. Still missing, and
deliberately not attempted here:

* an augmentation `ε` for `alternatingCofaceMapComplex`, dual to
  `AlternatingFaceMapComplex.ε`, so that "the augmented complex" is a statement rather than
  an assembly of pieces at each use;
* the transport of an extra degeneracy along a *contravariant* functor. `ExtraDegeneracy.map`
  takes a covariant `C ⥤ D`, and the functor in play for Čech cohomology —
  `FormalCoproduct.evalOp` applied to a presheaf — is contravariant on the site. The
  op-juggling this needs is mechanical but is not free;
* the positive-degree exactness corollary that #13 actually consumes.

Nothing here is stated for augmented objects at all: the isomorphism is between the two
unaugmented complexes, which is what makes it cheap.

## References

* `Mathlib/AlgebraicTopology/ExtraDegeneracy.lean` — the simplicial theory this reaches
* `Mathlib/CategoryTheory/Limits/FormalCoproducts/ExtraDegeneracy.lean` — the Čech object's
  extra degeneracy, already upstream
-/

universe v u

open CategoryTheory Opposite Simplicial

namespace AlgebraicTopology

namespace AlternatingCofaceMapComplex

variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- The alternating coface map complex of a cosimplicial object `Y` in `A`, made opposite, is
the alternating face map complex of `Y` viewed as a simplicial object in `Aᵒᵖ`.

Degreewise both sides are `Y.obj ⦋n⦌`, and both differentials are `∑ i, (-1) ^ i • δ i`; the
proof is that `op` distributes over that sum. -/
noncomputable def opIso (Y : CosimplicialObject A) :
    ((alternatingCofaceMapComplex A).obj Y).op ≅ (alternatingFaceMapComplex Aᵒᵖ).obj Y.op :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    rintro i j (rfl : j + 1 = i)
    simp [AlternatingFaceMapComplex.objD, AlternatingCofaceMapComplex.obj,
      AlternatingCofaceMapComplex.objD, SimplicialObject.δ, CosimplicialObject.δ,
      CochainComplex.of_d, op_sum, op_zsmul]
    rfl)

@[simp]
lemma opIso_hom_f (Y : CosimplicialObject A) (n : ℕ) :
    (opIso Y).hom.f n = 𝟙 _ :=
  rfl

@[simp]
lemma opIso_inv_f (Y : CosimplicialObject A) (n : ℕ) :
    (opIso Y).inv.f n = 𝟙 _ :=
  rfl

end AlternatingCofaceMapComplex

end AlgebraicTopology
