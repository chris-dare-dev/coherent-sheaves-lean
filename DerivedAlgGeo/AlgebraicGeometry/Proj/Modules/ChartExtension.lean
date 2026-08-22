/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Extension
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The degree-one chart, as seen by the affine extension lemma

`#585`'s chart step. A section of a quasi-coherent `F` over `D₊(g) ⊓ D₊(f)` extends to a section
over `D₊(g)` after clearing a power of `f / g`. `Modules/Affine/Extension.lean` supplies the
algebra; what is here is the geometry that lets it be applied, and the naming that lets it
elaborate.

## The geometry is two rewrites

`degreeOneChart_image_top` and `degreeOneChart_image_basicOpen` say the chart covers exactly
`D₊(g)` and meets `D₊(f)` in `D₊(g) ⊓ D₊(f)`. Both fall out of
`Scheme.Hom.image_preimage_eq_opensRange_inf` and `opensRange_awayι`, with
`Proj.awayι_preimage_basicOpen` naming the element: for `f` and `g` both of degree one it is
exactly `f / g`. Translating sections across the chart is free, because
`Scheme.Modules.restrictAppIso` is `Iso.refl`.

## The naming is not cosmetic

Stated inline, `IsIso (F.restrict (degreeOneChart 𝒜 hg)).fromTildeΓ` **does not elaborate**: it
runs `isDefEq` past 1.6M heartbeats and gives up, and pinning the arguments explicitly
(`references/instance-transparency.md` technique 7) does not rescue it. This is the
`Scheme.Modules` wrapper that `Modules/Affine/Equivalence.lean` documents.

Technique 5 fixes it, in two steps, and the second is the one that is easy to miss:

* `chartRestrict` names the restriction at an explicit result type, so the wrapper is crossed once
  here rather than at every use site;
* that alone is not enough — but it converts the timeout into a *fast, precise* mismatch, which is
  itself the argument for the technique. `fromTildeΓ` quantifies over `(Spec (.of ↑R)).Modules`
  with `R : CommRingCat`, and Lean cannot invert the coercion to solve `↑?R ≡ Away 𝒜 g`. So the
  result type is written through `chartRing`, a reducible `abbrev` for the bundled ring, and `?R`
  is then matched syntactically.

With that, the instance and the theorem each elaborate in seconds.

## Scope

One chart, one other basic open. `#585` is not closed: choosing a single `n` across a finite cover
of degree-one charts, and the passage from `(f / g)ⁿ ·` to multiplication into the twist `F(n)` by
`twistBy`, are not here.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Proj

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

/-- The degree-one chart through `g`. -/
noncomputable abbrev degreeOneChart {g : A} (hg : g ∈ 𝒜 1) :
    Spec (.of <| HomogeneousLocalization.Away 𝒜 g) ⟶ Proj 𝒜 :=
  awayι 𝒜 g hg Nat.one_pos

/-- **The chart covers exactly its own basic open.** -/
theorem degreeOneChart_image_top {g : A} (hg : g ∈ 𝒜 1) :
    degreeOneChart 𝒜 hg ''ᵁ ⊤ = basicOpen 𝒜 g := by
  rw [show (⊤ : (Spec (.of <| HomogeneousLocalization.Away 𝒜 g)).Opens) =
      degreeOneChart 𝒜 hg ⁻¹ᵁ ⊤ from rfl,
    Scheme.Hom.image_preimage_eq_opensRange_inf, inf_top_eq,
    opensRange_awayι 𝒜 g hg Nat.one_pos]

/-- **A second chart meets the first in the intersection of their basic opens** — the open the
affine extension lemma is applied over. -/
theorem degreeOneChart_image_basicOpen {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) :
    degreeOneChart 𝒜 hg ''ᵁ
        PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem hg hf) =
      basicOpen 𝒜 g ⊓ basicOpen 𝒜 f := by
  rw [← awayι_preimage_basicOpen 𝒜 hg Nat.one_pos hf Nat.one_pos,
    Scheme.Hom.image_preimage_eq_opensRange_inf, opensRange_awayι 𝒜 g hg Nat.one_pos]

/-! ### Naming the restriction

`references/instance-transparency.md` technique 5: naming the value with an explicit result type
stops the `Scheme.Modules` wrapper being crossed at every use site. Stating the restriction inline
makes instance search solve for the chart ring *and* peel the wrapper at once, which does not
terminate. -/

/-- The chart's degree-zero away ring, bundled.

Reducible, and written through rather than inlined, so that `fromTildeΓ`'s `R : CommRingCat` is
matched syntactically rather than by inverting a coercion. It takes `g` and not a proof about it:
the ring does not depend on the degree. -/
noncomputable abbrev chartRing (g : A) : CommRingCat.{u} :=
  .of (HomogeneousLocalization.Away 𝒜 g)

/-- **The restriction of `F` to the degree-one chart through `g`, named at its result type.** -/
noncomputable def chartRestrict (F : (Proj 𝒜).Modules) {g : A} (hg : g ∈ 𝒜 1) :
    (Spec (.of ↑(chartRing 𝒜 g))).Modules :=
  F.restrict (degreeOneChart 𝒜 hg)

instance chartRestrict_isQuasicoherent (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {g : A} (hg : g ∈ 𝒜 1) : (chartRestrict 𝒜 F hg).IsQuasicoherent :=
  inferInstanceAs ((F.restrict (degreeOneChart 𝒜 hg)).IsQuasicoherent)

instance isIso_fromTildeΓ_chartRestrict (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {g : A} (hg : g ∈ 𝒜 1) : IsIso (chartRestrict 𝒜 F hg).fromTildeΓ :=
  Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _

/-- **The affine extension lemma, over a degree-one chart.**

`s` lives over `D₊(g) ⊓ D₊(f)`, which in the chart is the basic open of `f / g`; a power of that
element carries it to a section over the whole chart, i.e. over `D₊(g)`. -/
theorem exists_pow_smul_eq_res_chart (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from F)]
    {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (s : (modulesSpecToSheaf.obj (chartRestrict 𝒜 F hg)).presheaf.obj
        (op (PrimeSpectrum.basicOpen
          (HomogeneousLocalization.Away.isLocalizationElem hg hf)))) :
    ∃ (n : ℕ) (t : (modulesSpecToSheaf.obj (chartRestrict 𝒜 F hg)).presheaf.obj (op ⊤)),
      (modulesSpecToSheaf.obj (chartRestrict 𝒜 F hg)).presheaf.map (homOfLE le_top).op t =
        HomogeneousLocalization.Away.isLocalizationElem hg hf ^ n • s :=
  Scheme.Modules.exists_pow_smul_eq_res_of_top_of_isQuasicoherent _ _ s

end AlgebraicGeometry.Proj
