/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Shift.ShiftedHomOpposite

/-!
# `R`-linearity of the opposite category and of the opposite shift

Every declaration here is the `R`-linear counterpart of an additive one Mathlib
already has, written in the `ForMathlib` pattern this repository uses for
Mathlib gaps (see `LinearAlgebra/Matrix/PolarDecomposition.lean`): supplied
because Mathlib
lacks it at the pin, and written to be upstreamable rather than convenient
here. Nothing in it mentions a stability condition or a Fourier--Mukai kernel.

It is filed under `Triangulated/` because that is what it is for -- the shift on
`Cᵒᵖ` and the `k`-linear Yoneda shift sequence next door. The bare
`Linear R Cᵒᵖ` instance is not itself triangulated, and its natural upstream
home is `Mathlib/CategoryTheory/Linear/`.

## What is here, and what it mirrors

| here | Mathlib's additive counterpart |
|---|---|
| `Linear R Cᵒᵖ` | `instPreadditiveOpposite` (`Preadditive/Opposite.lean`) |
| `Functor.op_linear` | `Functor.op_additive` (`Preadditive/Opposite.lean:110`) |
| `shiftFunctorOppositeLinear` | the `(shiftFunctor Cᵒᵖ n).Additive` instance (`Triangulated/Opposite/Basic.lean:67`) |
| `ShiftedHom.opEquiv_symm_smul` | `ShiftedHom.opEquiv_symm_add` (`Shift/ShiftedHomOpposite.lean:147`) |
| `ShiftedHom.opEquiv'_symm_smul` | `ShiftedHom.opEquiv'_symm_add` (`:154`) |

## Why the linear instance is not definitional

Morphisms in `Cᵒᵖ` are `Opposite`-wrapped: `(X ⟶ Y)` is `(Y.unop ⟶ X.unop)ᵒᵖ`.
`Preadditive Cᵒᵖ` transports the `AddCommGroup` along `Quiver.Hom.opEquiv`, so
the additive structure on `X ⟶ Y` is already pinned to that transport, and a
`Module R (X ⟶ Y)` has to be built *over that particular `AddCommGroup`*.
`Equiv.module` will not serve: it carries its own `Equiv.addCommMonoid`, which
is a different term from the one `Preadditive Cᵒᵖ` installed. So the module
structure is written out, with `smul r f = (r • f.unop).op` and every axiom
discharged through `Quiver.Hom.unop_inj`.

## What this file does not assert

Nothing about when `Cᵒᵖ` is *pretriangulated* or *linear over a field*, and no
comparison between this instance and any other route to `Module R (X ⟶ Y)` --
in particular `Preadditive.moduleEndLeft`, which is a module over `(End X)ᵐᵒᵖ`
and unrelated.

`shiftFunctorOppositeLinear` says the shift functors on `Cᵒᵖ` are `R`-linear
*given that those on `C` are*. It does not construct the latter, which is a
genuine hypothesis Mathlib carries everywhere it needs it
(`Triangulated/Basic.lean`, `Shift/ShiftedHom.lean`, `Shift/Linear.lean`) and
discharges only for concrete categories such as `CochainComplex` and, along
`Shift.linear_of_localization`, their localizations.
-/

namespace CategoryTheory

open Opposite

section LinearOpposite

variable (R : Type*) [Semiring R] (C : Type*) [Category C] [Preadditive C]
  [Linear R C]

/-- The `R`-module structure on `X ⟶ Y` in `Cᵒᵖ`, built over the `AddCommGroup`
that `Preadditive Cᵒᵖ` already installed.

Split out from `linearOpposite` rather than inlined so that each axiom can be
stated with an explicit `show`: inside a structure instance the `smul` field is
not yet available to `simp`, which therefore makes no progress on any of the
six goals. -/
instance homModuleOpposite (X Y : Cᵒᵖ) : Module R (X ⟶ Y) where
  smul r f := (r • f.unop).op
  one_smul f := Quiver.Hom.unop_inj (by
    show (1 : R) • f.unop = f.unop
    rw [one_smul])
  mul_smul r s f := Quiver.Hom.unop_inj (by
    show (r * s) • f.unop = r • (s • f.unop)
    rw [mul_smul])
  smul_zero r := Quiver.Hom.unop_inj (by
    show r • (0 : X ⟶ Y).unop = (0 : X ⟶ Y).unop
    simp)
  smul_add r f g := Quiver.Hom.unop_inj (by
    show r • (f + g).unop = ((r • f.unop).op + (r • g.unop).op).unop
    simp [smul_add])
  add_smul r s f := Quiver.Hom.unop_inj (by
    show (r + s) • f.unop = ((r • f.unop).op + (s • f.unop).op).unop
    simp [add_smul])
  zero_smul f := Quiver.Hom.unop_inj (by
    show (0 : R) • f.unop = (0 : X ⟶ Y).unop
    simp)

/-- **The opposite of an `R`-linear category is `R`-linear.**

The `R`-linear counterpart of `Preadditive Cᵒᵖ`, and the missing instance
`ShiftedHom.opEquiv`'s `smul` lemmas and the `k`-linear Yoneda `ShiftSequence`
both need. Scalars act through `unop`; the two compatibility fields swap
pre- and post-composition, because composition in `Cᵒᵖ` does. -/
instance linearOpposite : Linear R Cᵒᵖ where
  homModule := homModuleOpposite R C
  smul_comp _ _ _ r f g := Quiver.Hom.unop_inj (by
    show g.unop ≫ (r • f.unop) = r • (g.unop ≫ f.unop)
    rw [Linear.comp_smul])
  comp_smul _ _ _ f r g := Quiver.Hom.unop_inj (by
    show (r • g.unop) ≫ f.unop = r • (g.unop ≫ f.unop)
    rw [Linear.smul_comp])

variable {R C}

@[simp]
theorem unop_smul {X Y : Cᵒᵖ} (r : R) (f : X ⟶ Y) : (r • f).unop = r • f.unop :=
  rfl

@[simp]
theorem op_smul {X Y : C} (r : R) (f : X ⟶ Y) : (r • f).op = r • f.op :=
  rfl

end LinearOpposite

section OppositeFunctor

/-- The opposite of an `R`-linear functor is `R`-linear.

The counterpart of `Functor.op_additive`, and like it the proof body is empty:
with `linearOpposite` in scope, scalars on both sides are the ones on `C` and
`D` wrapped in `op`, so the field is closed by the tactic default.

Two spelling constraints, both worth recording because neither is obvious.
Section variables are included in order of first use, so an `[F.Linear R]`
binder introduces `R` only *after* `[Linear R C]` would have had to be
included — hence every binder is written out rather than taken from a
`variable` block. And declaring into the `Functor` namespace makes a bare
`Linear` resolve to `Functor.Linear`, so the category-level instances have to
be qualified. -/
instance Functor.op_linear {R : Type*} [Semiring R] {C D : Type*} [Category C]
    [Category D] [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    (F : C ⥤ D) [F.Linear R] : F.op.Linear R where

end OppositeFunctor

section OppositeShift

open Pretriangulated.Opposite

variable (R : Type*) [Semiring R] (C : Type*) [Category C] [Preadditive C]
  [Linear R C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R]

/-- **The shift functors on `Cᵒᵖ` are `R`-linear when those on `C` are.**

The `R`-linear counterpart of Mathlib's `(shiftFunctor Cᵒᵖ n).Additive`
instance, and the piece that makes `Linear R Cᵒᵖ` more than a bare module
structure: without it the opposite category is linear but its shift is not
known to respect scalars, which is exactly what the `k`-linear Yoneda shift
sequence needs.

Shifting by `n` on `Cᵒᵖ` *is* shifting by `-n` on `C`, opposed --
`shiftFunctorOpIso` witnesses this as an `eqToIso` of a definitional equality --
so `Functor.op_linear` applied to `shiftFunctor C (-n)` is already the instance,
and `inferInstanceAs` is the whole proof. -/
instance shiftFunctorOppositeLinear (n : ℤ) : (shiftFunctor Cᵒᵖ n).Linear R :=
  inferInstanceAs <| ((shiftFunctor C (-n)).op).Linear R

end OppositeShift

namespace ShiftedHom

open Pretriangulated.Opposite

variable {C : Type*} [Category C] [HasShift C ℤ] {X Y : C}
  {R : Type*} [Ring R] [Preadditive C] [Linear R C]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, Functor.Linear R (shiftFunctor C n)]

omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
set_option backward.defeqAttrib.useBackward true in
/-- The `smul` counterpart of `ShiftedHom.opEquiv_symm_add`.

The `set_option` mirrors Mathlib's on the additive twin, and is load-bearing for
the same reason: `dsimp` on an opposite-category shift leaves the goal not
type-correct at `instances` transparency, and the rewrite then cannot match. -/
@[simp]
lemma opEquiv_symm_smul {n : ℤ} (r : R)
    (x : ShiftedHom (Opposite.op Y) (Opposite.op X) n) :
    (opEquiv n).symm (r • x) = r • (opEquiv n).symm x := by
  dsimp [opEquiv_symm_apply]
  rw [← Linear.comp_smul, Functor.map_smul]

omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
set_option backward.defeqAttrib.useBackward true in
/-- The `smul` counterpart of `ShiftedHom.opEquiv'_symm_add`. -/
@[simp]
lemma opEquiv'_symm_smul {n a : ℤ} (r : R)
    (x : (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧)) (a' : ℤ) (h : n + a = a') :
    (opEquiv' n a a' h).symm (r • x) = r • (opEquiv' n a a' h).symm x := by
  dsimp [opEquiv']
  rw [opEquiv_symm_smul, Linear.smul_comp]

end ShiftedHom

end CategoryTheory
