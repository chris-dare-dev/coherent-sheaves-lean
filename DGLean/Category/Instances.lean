/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Algebra.Bilinear
import DGLean.Category.Basic

/-!
# A non-vacuous dg category

`DGCategory` is a structure with five axioms, and a structure with five axioms
is worth exactly nothing until something satisfies them. This file exhibits an
instance on an arbitrary object type, so the axiom set is proved consistent
before anything is built on top of it.

## The example

`Const k X` has `X` as its objects and, between any two of them, the cochain
complex that is `k` in every degree with zero differential. Composition is
multiplication in `k` and the identity is `1`.

This is a real dg category, not a degenerate one: its Hom-complexes are the
graded algebra with `k` in every degree, and every axiom has content —
associativity is `mul_assoc`, the unit laws are `one_mul` and `mul_one`. The
differential is zero, so the Leibniz rule and the cocycle condition hold for
the uninteresting reason, which is the honest thing to say about them.

## An idiom this file establishes

`ModuleCat.of k k`'s carrier is not transparent to instance search, so a goal
stated on `↑((constComplex k).X p)` cannot use `mul_assoc` or `zero_mul`: the
`Semigroup` and `MulZeroClass` instances are not found. Two things work, and
both are used below. For a term proof, pin the type on the lemma —
`mul_assoc (G := k) f g h`. For a tactic proof, bind the arguments at type `k`
in the field's lambda — `fun p _ _ _ _ _ (f : k) (g : k) => ...` — after which
the whole goal is about `k` and ordinary `simp` works. Rewriting the carrier in
place with `ModuleCat.coe_of` does **not** work: it breaks type-correctness of
the surrounding term.

What this example does **not** do is exercise the Leibniz rule against a
non-zero differential. That has to wait for `C^dg` in `dg-enhancements-e4`,
where the differential is the one on the Hom complex. Until then, treat the
Leibniz axiom as untested by any instance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory

variable (k : Type w) [CommRing k]

/-- The cochain complex that is `k` in every degree, with zero differential. -/
@[simps]
def constComplex : CochainComplex (ModuleCat.{w} k) ℤ where
  X _ := ModuleCat.of k k
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

/-- Objects for the dg category `constComplex` presents. A type synonym, so
that giving it a `DGCategory` instance does not attach one to `X` itself. -/
def Const (X : Type u) : Type u := X

namespace Const

instance dgCategory (X : Type u) : DGCategory.{w} k (Const X) where
  dgHom _ _ := constComplex k
  dgId _ := (1 : k)
  dgComp _ _ _ _ := LinearMap.mul k k
  dgComp_assoc _ _ _ _ _ _ _ _ _ f g h := mul_assoc (G := k) f g h
  dgId_comp _ f := one_mul (M := k) f
  dgComp_id _ f := mul_one (M := k) f
  dgId_cocycle _ := rfl
  dgComp_leibniz := fun p _ _ _ _ _ (f : k) (g : k) => by
    show (0 : k) = (0 : k) * g + p.negOnePow • (f * (0 : k))
    simp

end Const
