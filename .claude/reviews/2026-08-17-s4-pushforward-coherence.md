# S4 step 2 — the affine case, proved; the globalization, measured — 2026-08-17 (UTC)

For #572. This continues the lane opened by `2026-08-17-s4-projective-variety-lane.md`.

## What is proved

`DerivedAlgGeo/AlgebraicGeometry/CoherentSheaf/Pushforward/Affine.lean`:

```
isCoherent_pushforward_of_surjective [IsNoetherianRing R] (hφ : Function.Surjective φ.hom) :
  Scheme.Modules.IsCoherent (Spec S) M →
  Scheme.Modules.IsCoherent (Spec R) ((Scheme.Modules.pushforward (Spec.map φ)).obj M)
```

with `gammaPushforwardIso` and `moduleFinite_gammaPushforward` as the two steps.

This is the mathematical content of step 2. Coherence of the pushforward is not a locality
statement about `φ`; it holds because the pushforward **is** the tilde of a finitely generated
module over a noetherian ring, and all three ingredients are at the pin:

* `Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent` — a coherent sheaf on an affine is a tilde;
* `AlgebraicGeometry.isIso_fromTildeΓ_pushforward` (`Modules/Tilde.lean:553`) — being a tilde
  survives pushforward along `Spec.map`. Mathlib's own TODO above it says this is what it is for;
* `AlgebraicGeometry.pushforwardCompModulesSpecToSheafIso` (`Modules/Tilde.lean:529`) — evaluated
  at `⊤`, the global sections of the pushforward are the global sections of the original with the
  base ring acting through `φ`.

Surjectivity is used **only** to get `Module.Finite R S`. The theorem is really about finite
morphisms; the statement is phrased with surjectivity because that is what a closed immersion
supplies (`Morphisms/ClosedImmersion.lean:361`).

## Two traps, both in the source

`ModuleCat.restrictScalars` leaves the carrier type alone, so `RestrictScalars.isScalarTower`
does not apply to its object and `IsScalarTower R S ((restrictScalars φ).obj X)` has to be given
by hand. It is `mul_smul` after `Algebra.smul_def`, but instance search will not find it.

For the same reason `Module.Finite S ((restrictScalars φ).obj X)` does not fire from
`Module.Finite S X`; it needs an explicit `inferInstanceAs`.

A dead end that looks shorter and is not: `Module.Finite.of_restrictScalars_finite` goes the wrong
way (finite over the *smaller* ring implies finite over the larger). The direction needed here is
`Module.Finite.trans`, which is why the tower is unavoidable.

## What the globalization still needs

Step 2 in full — `ι_* F` coherent on `Pⁿ` for a closed immersion `ι` — reduces to the affine case
by `Modules.isCoherent_iff_restrict_affineOpenCover` (`CoherentSheaf/Descent/Locality.lean:176`),
which is already in the tree. Two gaps stand between:

1. **Pushforward does not commute with restriction to an open, in the tree.** The criterion asks
   for `((ι_* F).restrict (𝒰.f i))` finitely presented, and what the affine theorem gives is the
   pushforward along the restricted morphism `ι⁻¹(V) ⟶ V`. The comparison isomorphism between
   those two — base change of a pushforward along an open immersion — is not in the tree and was
   not found at the pin.
2. **The restricted morphism has to be recognized as `Spec.map` of a surjection.** `IsAffineHom`
   (free from `IsClosedImmersion`, `Morphisms/ClosedImmersion.lean:149`) makes `ι⁻¹(V)` affine, and
   `Morphisms/ClosedImmersion.lean:361` supplies surjectivity on affine opens' sections. What is
   missing is the identification of a morphism of affine schemes with `Spec.map` of its `Γ`, in the
   form the affine theorem consumes.

Neither is deep; both are plumbing of the kind that takes a session each. They are the next two
slices, in that order.

## Step 3 is untouched, and is not adjacent to this

`Hⁱ(X, F) ≅ Hⁱ(Pⁿ, ι_* F)` needs exactness and acyclicity of the closed-immersion pushforward
against the small site's `Sheaf.H`, with the `HasExt` universe a parameter — the convention hazard
#569 records. Nothing proved here shortens it: this file is about finite presentation, not about
derived functors.
