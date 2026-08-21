# When an instance that should obviously fire does not

An instance search failure that looks impossible — the types are equal, `rfl`
proves it, and the instance is right there — is almost always one thing in this
repository. It has been rediscovered six times in five subsystems. This note
exists so there is not a seventh.

## The failure

**Instance search unifies at `reducible` transparency.** A `def`, a
`CompleteLattice.copy`, or an `X.of` that wraps a canonical type without
`@[reducible]` does not unfold there. So an instance stated about the wrapped
type is invisible to a goal stated about the wrapper, and vice versa — while
`rfl` still proves the two types equal, which is why nothing looks wrong.

The diagnostic is two lines:

```lean
example : A = B := rfl                      -- succeeds: defeq at default
example : A = B := by with_reducible rfl    -- fails: not defeq at reducible
```

If the first passes and the second fails, this is the problem, and no amount of
`haveI` will help: the defeq is accepted when it is *checked*, but search never
gets far enough to check it.

## Where it has already bitten

| Opaque type | What silently fails | File | Issue |
|---|---|---|---|
| `Coh X` — `def` over `FullSubcategory` | every Mathlib instance needing `[Abelian C]` *and* another `Preadditive`-parameterised class | `AlgebraicGeometry/CoherentSheaf/Abelian/Basic.lean` | #662 open |
| `Scheme.Modules` — `def` over `SheafOfModules` | `Epi`, `Mono`, `PreservesZeroMorphisms`, `PreservesFiniteLimits` | `AlgebraicGeometry/Modules/Affine/Equivalence.lean` | #59 closed |
| `Opens X`'s `CompleteLattice.copy` | `OrderTop`, `BoundedOrder`, hence **every limit instance on the site `X.Opens`** | `Topology/Opens/Limits.lean` | — |
| `AddCommGrpCat.of ℤ` carrier | `Semigroup`, hence `mul_assoc` | `CategoryTheory/DGCategory/Instances.lean` | — |
| `AddCommGrpCat.of (_ × _)` carrier | `Prod.fst_add` will not fire | `CategoryTheory/DGCategory/Product.lean` | — |
| `Γ(Proj 𝒜, U)` vs structure-sheaf sections | `Module`, hence any `•` on associated-sheaf sections | `AlgebraicGeometry/Cohomology/Finiteness/ProjectiveSpaceCechScalars.lean` | #678 |

Not this pattern, though it reads like it: the `HasExt.{u}` / `HasExt.{u + 1}`
sites across the Čech lane. Those pass the witness positionally to stop search
picking *between two genuinely different groups*. That is universe
disambiguation, not transparency.

## What to do about it

Ordered by blast radius. Prefer the earliest one that closes the goal.

1. **Pin the type on the lemma.** `mul_assoc (G := ℤ) f g h`. For a tactic
   proof, bind the arguments at the plain type in the field's lambda so the goal
   is about `ℤ` and ordinary `simp` works. (`DGCategory/Instances.lean`)
2. **Restate the projection lemmas at the type the goals actually have** — not
   at the type it unfolds to. (`DGCategory/Product.lean`)
3. **Build at plain types and apply to the carriers.** Term elaboration unifies
   up to defeq, so this works where search does not.
   (`DGCategory/Product.lean`)
4. **State the fact in the form that elaborates.** On associated-sheaf sections,
   write scalar actions with `varietyScalarAction`'s `app` and convert to `•`
   with `varietyScalarAction_app_eq` inside the proof, where the expected type
   is already fixed. (`ProjectiveSpaceCechScalars.lean`)
5. **Name the value with an explicit result type**, so the wrapper is never
   crossed at a use site. `constSectionOn` is one; `Scheme.Modules.toSheaf` is
   the one that scales, because downstream code writes it and never meets the
   boundary. (`Affine/Equivalence.lean` calls this out as the technique that
   generalises.)
6. **Name explicit projections, `private`.** (`Opens/Limits.lean` —
   deliberately private, because a global `OrderTop` on `Opens` would be a
   data-carrying diamond that could break existing `simp` lemmas about `⊤`.)
7. **Supply the argument explicitly at default transparency**, e.g.
   `@DerivedCategory.instLinear k _ (Coh Y.toScheme) _ _ (cohLinear Y) _`. Fixes
   one term and nothing else. (`CoherentSheaf/Linear.lean`)

## What not to do

**Do not add a second instance over the other spelling.** Two instances that are
defeq at default but not at reducible is not a fix, it is the same bug pointing
the other way: lemmas stated against one stop applying to goals carrying the
other. That is exactly what #662 documents for `Coh X`.

## The root fix, and why it keeps not happening

Make the wrapper `@[reducible]` (or an `abbrev`). Three files reached this
independently:

* #662, candidate fix 1 — *"Make `Coh` an `abbrev`. Instance search then sees
  `FullSubcategory` directly… Smallest edit, widest blast radius."*
* `Affine/Equivalence.lean` — *"Making `Scheme.Modules` and
  `Scheme.Modules.Hom` `@[reducible]` upstream would remove the problem at the
  root and is the honest fix, but it is a Mathlib change with its own
  performance question."*
* `Opens/Limits.lean` — declines the global instance for the diamond risk.

Every declension is for one of two reasons: the fix belongs upstream in Mathlib,
or it changes elaboration across a whole subtree and wants a full `lake build`
to see the fallout. Both are real. Neither is a reason to rediscover the
diagnosis a seventh time, which is what this note is for.

Note that `mathlib-style.md` §3 says definitions stay `semireducible` unless
there is a stated reason. Wrapping a type that carries instances **is** a stated
reason; that is the case this note is about.
