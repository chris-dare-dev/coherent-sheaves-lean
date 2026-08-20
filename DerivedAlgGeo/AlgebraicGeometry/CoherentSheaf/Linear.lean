/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.FiniteDimensional
import DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families.BoundedGeometry
import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Module sheaves on a variety are `k`-linear

On a variety over `k`, multiplication by a global function is an endomorphism of
every module sheaf, and it commutes with every morphism. Composing that with the
ring map `k → Γ(X, O_X)` supplied by the structure morphism makes every
`Hom`-group a `k`-module, compatibly with composition — that is, it makes
`X.Modules` a `k`-linear category, and `Coh X` with it.

Every ingredient was already here. `Cohomology.globalSectionSmul`,
`globalSectionAction`, `baseFieldToGlobalSections`, `varietyScalarAction` and
`varietyScalarAction_naturality` were built to give coherent cohomology its
`k`-structure; this file observes that the same action makes the *category*
linear, which is a strictly stronger statement and one nothing had recorded.

## Why this is worth its own file

Because of what it unlocks rather than what it says. Mathlib's
`DerivedCategory.Linear` gives `Linear R (DerivedCategory C)` from
`Linear R C`, and `Linear.fullSubcategory` propagates to
`DerivedCategory.Bounded C`, which is a `FullSubcategory` of it. So the single
instance below is the whole distance between "`Hom` in `Dᵇ(Coh X)` is an abelian
group" and "`Hom` in `Dᵇ(Coh X)` is a `k`-vector space".

That was the one obstruction to *stating* what a spherical object is:
`Hom(E, E⟦i⟧) ≅ k` is not expressible against an `AddCommGrp`, and
`Numerical/GrothendieckGroup/MukaiVector.lean`'s docstring names exactly this
gap when it says sphericity of an object needs an `Ext` that layer does not
have.

## What this does not give

Finite-dimensionality. `Linear k` says the `Hom`-groups are `k`-modules, not
that they are finite-dimensional, and nothing here bounds them.
`FiniteDimensionalCohomology` remains supplied data, and the projective case is
issue #332. A `Hom`-group being a `k`-vector space of unknown dimension is
exactly enough to *state* sphericity and not enough to prove anything about it.

Nor does it give a trace, a Serre functor, or any duality. Those need the
finiteness this file does not supply.

## Main results

* `Variety.modulesLinear` — `X.Modules` is `k`-linear.
* `Variety.cohLinear` — `Coh X` is `k`-linear, inherited as a full subcategory.
* `Variety.smul_eq_action_comp` — the scalar action unfolds to precomposition
  with multiplication by the corresponding global function, which is the only
  fact a caller needs in order to compute with it.
* `Variety.derivedLinear` — `Dᵇ(Coh X)` is `k`-linear, so `Hom(E, F⟦i⟧)` is a
  `k`-vector space. Stated explicitly rather than inferred; the section comment
  above it records the instance diamond that stops search finding it.
-/

universe u

open CategoryTheory AlgebraicGeometry.Cohomology

namespace AlgebraicGeometry

namespace Variety

variable {k : Type u} [Field k] (Y : Variety k)

/-- Morphisms of module sheaves on a variety form a `k`-module, by precomposing
with multiplication by the corresponding global function.

Precomposition rather than postcomposition is an arbitrary choice;
`varietyScalarAction_naturality` says the two agree, and `comp_smul` below is
where that is spent. -/
@[reducible]
noncomputable def homModule (M N : Y.toScheme.Modules) : Module k (M ⟶ N) where
  smul r f := varietyScalarAction Y M r ≫ f
  one_smul f := by
    show varietyScalarAction Y M 1 ≫ f = f
    rw [map_one]
    exact Category.id_comp f
  mul_smul r s f := by
    show varietyScalarAction Y M (r * s) ≫ f
      = varietyScalarAction Y M r ≫ varietyScalarAction Y M s ≫ f
    rw [mul_comm, map_mul, End.mul_def, Category.assoc]
  smul_zero r := by
    show varietyScalarAction Y M r ≫ (0 : M ⟶ N) = 0
    exact Limits.comp_zero
  smul_add r f g := by
    show varietyScalarAction Y M r ≫ (f + g)
      = varietyScalarAction Y M r ≫ f + varietyScalarAction Y M r ≫ g
    exact Preadditive.comp_add _ _ _ _ _ _
  add_smul r s f := by
    show varietyScalarAction Y M (r + s) ≫ f
      = varietyScalarAction Y M r ≫ f + varietyScalarAction Y M s ≫ f
    rw [map_add]
    exact Preadditive.add_comp _ _ _ _ _ _
  zero_smul f := by
    show varietyScalarAction Y M 0 ≫ f = 0
    rw [map_zero]
    exact Limits.zero_comp

/-- **Module sheaves on a variety form a `k`-linear category.**

`smul_comp` is associativity. `comp_smul` is the only clause with content: it
says the action may be moved across a morphism, which is
`varietyScalarAction_naturality`, itself `globalSectionSmul_naturality` — the
statement that multiplication by a global function is central. -/
noncomputable instance modulesLinear : Linear k Y.toScheme.Modules where
  homModule M N := homModule Y M N
  smul_comp M N P r f g := by
    show (varietyScalarAction Y M r ≫ f) ≫ g = varietyScalarAction Y M r ≫ f ≫ g
    exact Category.assoc _ _ _
  comp_smul M N P f r g := by
    show f ≫ varietyScalarAction Y N r ≫ g = varietyScalarAction Y M r ≫ f ≫ g
    rw [← Category.assoc, ← varietyScalarAction_naturality Y f r, Category.assoc]

/-- The scalar action, unfolded. This is the computation rule for everything
above; `Linear k` alone says a `k`-module structure exists but not which one. -/
theorem smul_eq_action_comp {M N : Y.toScheme.Modules} (r : k) (f : M ⟶ N) :
    r • f = varietyScalarAction Y M r ≫ f :=
  rfl

/-- **Coherent sheaves on a variety form a `k`-linear category**, inherited from
the ambient module sheaves as a full subcategory.

Declared rather than inferred because `Coh` is a `def`, so instance search does
not see the `FullSubcategory` underneath it; the `Preadditive` and `Abelian`
instances next door are stated the same way. -/
noncomputable instance cohLinear : Linear k (Coh Y.toScheme) :=
  inferInstanceAs (Linear k (Scheme.coherent Y.toScheme).FullSubcategory)

/-! ### Propagation to the derived category

Mathlib's `DerivedCategory.instLinear` should fire on its own here, and does
not. The reason is a latent instance diamond in `Coh`, and it is worth stating
because it will block every Mathlib abelian-category instance that wants
`[Abelian C]` and `[Linear R C]` at once, not just this one.

`Coh.preadditive` is `inferInstanceAs (Preadditive …FullSubcategory)`, while
`Coh.abelian` is built by `change … ; infer_instance`, so its `toPreadditive`
is the preadditive field *of the full subcategory's `Abelian` instance*. The two
are defeq — `rfl` proves them equal — but **not at reducible transparency**,
which is the transparency instance search runs at. So `cohLinear`, whose type
mentions `Coh.preadditive`, does not match a goal whose `Preadditive` argument
came out of `Abelian`.

Supplying the argument explicitly resolves it, because elaboration checks that
application at default transparency. That is a workaround, not a fix: the fix is
to make the two instances reducibly equal, which means changing `Coh` or
`Coh.abelian` in `CoherentSheaf/Abelian/Basic.lean` and is deliberately not done
in the change that discovers the problem. -/

/-- The derived category of coherent sheaves on a variety is `k`-linear.

Stated explicitly rather than inferred; see the section comment for why search
cannot find it, and note that the workaround is confined to this one term. -/
noncomputable instance derivedLinear :
    Linear k (DerivedCategory (Coh Y.toScheme)) :=
  @DerivedCategory.instLinear k _ (Coh Y.toScheme) _ _ (cohLinear Y) _

end Variety

end AlgebraicGeometry
