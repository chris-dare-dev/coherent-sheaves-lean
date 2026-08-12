/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# The localisation criterion for the affine comparison theorem

On `Spec R`, a quasi-coherent sheaf of modules should be recovered from its global sections
by `~`: the counit `Scheme.Modules.fromTildeΓ` should be an isomorphism. This is Stacks
[01IA](https://stacks.math.columbia.edu/tag/01IA) / Hartshorne II.5.1, and it is missing from
Mathlib at `v4.29.0`.

This file reduces that theorem to a statement about localisation of modules, and proves the
reduction is *exact*: the counit is an isomorphism **if and only if** restriction to every
basic open is a localisation. `CohLean.AlgebraicGeometry.Modules.Affine.Gluing` proves that
quasi-coherence supplies this condition and completes the comparison theorem.

## Main results

* `TopCat.Presheaf.stalkFunctor_map_surjective_of_isBasis` and
  `TopCat.Sheaf.isIso_of_isIso_app_of_isBasis` — a morphism of sheaves that is an isomorphism
  on a basis is an isomorphism. Mathlib has the injectivity half
  (`stalkFunctor_map_injective_of_isBasis`) but neither the surjectivity half nor the
  conclusion.
* `AlgebraicGeometry.Scheme.Modules.basicOpenRestriction` — restriction of global sections to `D(f)`.
* `AlgebraicGeometry.isIso_fromTildeΓ_app_basicOpen` — the component of the counit at `D(f)`
  is an isomorphism exactly when that restriction is a localisation at the powers of `f`.
* `AlgebraicGeometry.isIso_fromTildeΓ_of_isLocalizedModule` — hence the counit is an
  isomorphism as soon as every such restriction is a localisation.
* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestriction_tilde` — the base
  case, `M = N^~`, where that hypothesis holds. It is both the starting point of the general
  argument and the check that the hypothesis is satisfiable rather than vacuous.
* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_isIso` — the
  converse of the reduction, obtained by transporting the base case along the counit.
* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_presentation` —
  the local input for the gluing argument: a global presentation makes every basic-open
  restriction a localisation.
* `AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_iff_isLocalizedModule` — the two put
  together: **`IsIso M.fromTildeΓ ↔ ∀ f, IsLocalizedModule (powers f) (restriction to D(f))`.**
  This is the statement to quote.

## Why this is the right reduction

`Scheme.Modules.fromTildeΓ` is *built* by `TopCat.Sheaf.restrictHomEquivHom` along
`PrimeSpectrum.isBasis_basic_opens`, with its component at `D(f)` given by
`IsLocalizedModule.lift`. Mathlib's `Scheme.Modules.toOpen_fromTildeΓ_app` records the
resulting triangle: the component composed with `tilde.toOpen` is the restriction map. Since
`tilde.toOpen` at `D(f)` is a localisation at `Submonoid.powers f` — Mathlib supplies that
instance — the component is the comparison map between two candidate localisations, and is an
isomorphism precisely when the second one is a localisation too.

Nothing in that argument needs quasi-coherence, and `tilde.isUnit_algebraMap_end_basicOpen` is
already stated in Mathlib for an *arbitrary* `M : (Spec R).Modules`, not only for tildes. So
the whole content of the comparison theorem is concentrated in the single hypothesis of
`isIso_fromTildeΓ_of_isLocalizedModule`.

## Completion

The mathematical implication deliberately left out of this reduction is:

> for `M` **quasi-coherent** on `Spec R` and `f : R`, the restriction `Γ(M, ⊤) → Γ(M, D(f))`
> exhibits its target as the localisation at `Submonoid.powers f`

equivalently, by `isIso_fromTildeΓ_iff_isLocalizedModule`, that a quasi-coherent sheaf on an
affine scheme lies in the essential image of `~`. It is proved in
`CohLean.AlgebraicGeometry.Modules.Affine.Gluing` as
`Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_isQuasicoherent`; the resulting
counit theorem is `Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`.

The completion is the classical covering argument: choose a finite basic-open subcover carrying
presentations, choose uniform powers of `f` for equality and extension, and glue the normalized
local lifts with the sheaf axiom. The scheme/slice transport used by its local input is in
`CohLean.AlgebraicGeometry.Modules.Restriction.OpenImmersion`.

## References

* [Stacks, Tag 01IA](https://stacks.math.columbia.edu/tag/01IA)
-/

universe v u

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] [Limits.HasColimits C] {X : TopCat.{v}}
  {FC : C → C → Type*} {CC : C → Type v} [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory C FC] [Limits.PreservesFilteredColimits (CategoryTheory.forget C)]
  {B : Set (Opens X)}

/-- Surjectivity on stalks may be checked on a basis.

The mirror image of Mathlib's `stalkFunctor_map_injective_of_isBasis`: every germ is
represented by a section over a basic open (`germ_exist_of_isBasis`), and a surjection there
lifts it. -/
lemma stalkFunctor_map_surjective_of_isBasis (hB : Opens.IsBasis B)
    {F G : Presheaf C X} {α : F ⟶ G}
    (hα : ∀ U ∈ B, Function.Surjective (ConcreteCategory.hom (α.app (op U)))) (x : X) :
    Function.Surjective (ConcreteCategory.hom ((stalkFunctor C x).map α)) := by
  intro t
  obtain ⟨U, hxU, hU, s, rfl⟩ := exists_mem_germ_eq_of_isBasis hB G x t
  obtain ⟨s', rfl⟩ := hα U hU s
  exact ⟨ConcreteCategory.hom (F.germ U x hxU) s', stalkFunctor_map_germ_apply U x hxU α s'⟩

end TopCat.Presheaf

namespace TopCat.Sheaf

/-- **A morphism of sheaves that is an isomorphism on a basis is an isomorphism.**

Checked on stalks: injectivity is Mathlib's `stalkFunctor_map_injective_of_isBasis` and
surjectivity is `stalkFunctor_map_surjective_of_isBasis` above.

The hypotheses are written out rather than taken from a `variable` block: `FC` and `CC` do
not appear in the statement, so `variable` auto-inclusion drops the `ConcreteCategory` and
`forget`-preservation binders along with them. -/
theorem isIso_of_isIso_app_of_isBasis
    {C : Type u} [Category.{v} C] [Limits.HasColimits C] {X : TopCat.{v}}
    {FC : C → C → Type*} {CC : C → Type v} [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    [Limits.PreservesFilteredColimits (CategoryTheory.forget C)]
    [Limits.HasLimits C] [Limits.PreservesLimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {B : Set (Opens X)} (hB : Opens.IsBasis B) {F G : Sheaf C X} (α : F ⟶ G)
    (hα : ∀ U ∈ B, IsIso (α.hom.app (op U))) : IsIso α := by
  haveI : ∀ x : X, IsIso ((Presheaf.stalkFunctor C x).map α.hom) := fun x => by
    have hinj : Function.Injective
        (ConcreteCategory.hom ((Presheaf.stalkFunctor C x).map α.hom)) :=
      Presheaf.stalkFunctor_map_injective_of_isBasis hB (fun U hU => by
        haveI := hα U hU
        exact ((ConcreteCategory.isIso_iff_bijective (α.hom.app (op U))).mp inferInstance).1) x
    have hsurj : Function.Surjective
        (ConcreteCategory.hom ((Presheaf.stalkFunctor C x).map α.hom)) :=
      Presheaf.stalkFunctor_map_surjective_of_isBasis hB (fun U hU => by
        haveI := hα U hU
        exact ((ConcreteCategory.isIso_iff_bijective (α.hom.app (op U))).mp inferInstance).2) x
    exact (ConcreteCategory.isIso_iff_bijective
      ((Presheaf.stalkFunctor C x).map α.hom)).mpr ⟨hinj, hsurj⟩
  exact Presheaf.isIso_of_stalkFunctor_map_iso α

end TopCat.Sheaf

namespace AlgebraicGeometry

open _root_.PrimeSpectrum

variable {R : CommRingCat.{u}}

namespace Scheme.Modules

/-- Restriction of the global sections of an `𝒪_{Spec R}`-module to the basic open `D(f)`.

This is the map the affine comparison theorem asserts to be a localisation at
`Submonoid.powers f`. -/
noncomputable def basicOpenRestriction (M : (Spec R).Modules) (f : R) :
    (modulesSpecToSheaf.obj M).presheaf.obj (op ⊤) ⟶
      (modulesSpecToSheaf.obj M).presheaf.obj (op (PrimeSpectrum.basicOpen f)) :=
  (modulesSpecToSheaf.obj M).presheaf.map (homOfLE (fun _ _ => trivial)).op

/-- The counit composed with `tilde.toOpen` is restriction — Mathlib's
`toOpen_fromTildeΓ_app`, phrased through `basicOpenRestriction`. -/
lemma toOpen_comp_fromTildeΓ_app (M : (Spec R).Modules) (f : R) :
    tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)) (PrimeSpectrum.basicOpen f) ≫
        (modulesSpecToSheaf.map M.fromTildeΓ).hom.app (op (PrimeSpectrum.basicOpen f)) =
      M.basicOpenRestriction f := by
  rw [toOpen_fromTildeΓ_app M (PrimeSpectrum.basicOpen f)]; rfl

/-- **The base case: for `M = N^~` the restriction to `D(f)` is a localisation.**

`tilde.toOpen N ⊤` is an isomorphism and `tilde.toOpen N ⊤ ≫ restriction = tilde.toOpen N D(f)`
by `tilde.toOpen_res`, so the restriction inherits the localisation property Mathlib already
proves for `tilde.toOpen N D(f)`.

This is what the general statement — the hypothesis of
`isIso_fromTildeΓ_of_isLocalizedModule` — has to be reduced to for a quasi-coherent `M`, and
it is also the check that that hypothesis is satisfiable rather than vacuous: feeding this
lemma to the reduction recovers `IsIso (tilde N).fromTildeΓ`, which Mathlib knows
independently. -/
instance isLocalizedModule_basicOpenRestriction_tilde (N : ModuleCat.{u} R) (f : R) :
    IsLocalizedModule (Submonoid.powers f) (basicOpenRestriction (tilde N) f).hom := by
  haveI : IsIso (tilde.toOpen N ⊤) := tilde.isIso_toOpen_top
  let e : N ≃ₗ[R] _ := (asIso (tilde.toOpen N ⊤)).toLinearEquiv
  haveI : IsLocalizedModule (Submonoid.powers f)
      ((basicOpenRestriction (tilde N) f).hom ∘ₗ (e : N →ₗ[R] _)) := by
    -- `tilde.toOpen_res` is `rfl`, so this is a definitional match.
    convert (inferInstance : IsLocalizedModule (Submonoid.powers f)
      (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom) using 1
    change (tilde.toOpen N ⊤ ≫ basicOpenRestriction (tilde N) f).hom =
      (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom
    exact congrArg ModuleCat.Hom.hom
      (tilde.toOpen_res N ⊤ (PrimeSpectrum.basicOpen f) _)
  have := IsLocalizedModule.of_linearEquiv_right (Submonoid.powers f)
    ((basicOpenRestriction (tilde N) f).hom ∘ₗ (e : N →ₗ[R] _)) e.symm
  simpa [LinearMap.comp_assoc] using this

end Scheme.Modules

/-- **The component of the counit at `D(f)` is an isomorphism when restriction to `D(f)` is a
localisation at the powers of `f`.**

Both `tilde.toOpen` and the restriction are then localisations of `Γ(M, ⊤)` at the same
submonoid, and the component is the comparison map between them. -/
theorem isIso_fromTildeΓ_app_basicOpen (M : (Spec R).Modules) (f : R)
    [IsLocalizedModule (Submonoid.powers f) (M.basicOpenRestriction f).hom] :
    IsIso ((modulesSpecToSheaf.map M.fromTildeΓ).hom.app (op (basicOpen f))) := by
  set N := (modulesSpecToSheaf.obj M).presheaf.obj (op ⊤) with hN
  have hunit := Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := M) f le_rfl
  have key := Scheme.Modules.toOpen_comp_fromTildeΓ_app M f
  have heq : ((modulesSpecToSheaf.map M.fromTildeΓ).hom.app (op (basicOpen f))).hom
      = (IsLocalizedModule.linearEquiv (Submonoid.powers f)
          (tilde.toOpen N (basicOpen f)).hom (M.basicOpenRestriction f).hom).toLinearMap := by
    refine IsLocalizedModule.ext (Submonoid.powers f) (tilde.toOpen N (basicOpen f)).hom
      (fun s => ?_) ?_
    · obtain ⟨n, hn⟩ := s.2
      rw [← hn, map_pow]
      exact hunit.pow n
    · ext x
      have := congrArg (fun (g : N ⟶ _) => g.hom x) key
      simpa using this
  have hbij : Function.Bijective
      ((modulesSpecToSheaf.map M.fromTildeΓ).hom.app (op (basicOpen f))).hom := by
    rw [heq]
    exact (IsLocalizedModule.linearEquiv _ _ _).bijective
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij

/-- **The counit is an isomorphism as soon as restriction to every basic open is a
localisation.**

This is the whole geometric content of the affine comparison theorem; what remains is to
discharge the hypothesis for quasi-coherent `M`, which is not done here — see the module
docstring. -/
theorem isIso_fromTildeΓ_of_isLocalizedModule (M : (Spec R).Modules)
    (h : ∀ f : R, IsLocalizedModule (Submonoid.powers f) (M.basicOpenRestriction f).hom) :
    IsIso M.fromTildeΓ := by
  haveI := (SpecModulesToSheafFullyFaithful (R := R)).full
  haveI := (SpecModulesToSheafFullyFaithful (R := R)).faithful
  suffices hiso : IsIso (modulesSpecToSheaf.map M.fromTildeΓ) from
    isIso_of_reflects_iso _ modulesSpecToSheaf
  refine TopCat.Sheaf.isIso_of_isIso_app_of_isBasis isBasis_basic_opens _ ?_
  rintro U ⟨f, rfl⟩
  haveI := h f
  exact isIso_fromTildeΓ_app_basicOpen M f

/-- `basicOpenRestriction` is a presheaf restriction map, so it is natural in `M`. -/
lemma Scheme.Modules.basicOpenRestriction_naturality {M N : (Spec R).Modules} (φ : M ⟶ N)
    (f : R) :
    M.basicOpenRestriction f ≫
        (modulesSpecToSheaf.map φ).hom.app (op (PrimeSpectrum.basicOpen f)) =
      (modulesSpecToSheaf.map φ).hom.app (op ⊤) ≫ N.basicOpenRestriction f :=
  (modulesSpecToSheaf.map φ).hom.naturality _

/-- **The converse of `isIso_fromTildeΓ_of_isLocalizedModule`.**

If `M` is in the essential image of `~` — equivalently, if its counit is an isomorphism — then
restriction to each basic open is a localisation, by transporting
`isLocalizedModule_basicOpenRestriction_tilde` across that isomorphism. -/
theorem Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_isIso (M : (Spec R).Modules)
    [IsIso M.fromTildeΓ] (f : R) :
    IsLocalizedModule (Submonoid.powers f) (M.basicOpenRestriction f).hom := by
  set N := (modulesSpecToSheaf.obj M).presheaf.obj (op ⊤) with hN
  -- `modulesSpecToSheaf` sends the counit to an isomorphism of sheaves; `sheafToPresheaf`
  -- carries that to the underlying natural transformation, and `NatIso.isIso_app_of_isIso`
  -- then makes every component invertible.
  haveI : IsIso (modulesSpecToSheaf.map M.fromTildeΓ) := inferInstance
  haveI : IsIso (modulesSpecToSheaf.map M.fromTildeΓ).hom := by
    change IsIso ((sheafToPresheaf _ _).map (modulesSpecToSheaf.map M.fromTildeΓ))
    infer_instance
  -- the naturality square, with both verticals invertible
  have key := Scheme.Modules.basicOpenRestriction_naturality (M := tilde N) (N := M)
    M.fromTildeΓ f
  let eTop := (asIso ((modulesSpecToSheaf.map M.fromTildeΓ).hom.app (op ⊤))).toLinearEquiv
  let eBas := (asIso ((modulesSpecToSheaf.map M.fromTildeΓ).hom.app
    (op (PrimeSpectrum.basicOpen f)))).toLinearEquiv
  -- restriction on `tilde N` is a localisation; push it across the two isomorphisms
  haveI h1 := IsLocalizedModule.of_linearEquiv (Submonoid.powers f)
    ((tilde N).basicOpenRestriction f).hom eBas
  haveI h2 := IsLocalizedModule.of_linearEquiv_right (Submonoid.powers f)
    (eBas.toLinearMap ∘ₗ ((tilde N).basicOpenRestriction f).hom) eTop.symm
  convert h2 using 1
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := eTop.surjective x
  have hy := congrArg (fun g => ModuleCat.Hom.hom g y) key
  simpa [eTop, eBas] using hy.symm

/-- A presented sheaf of modules on an affine scheme restricts to a localisation on every
basic open. This is the per-member input for gluing the affine comparison from a basic-open
cover carrying presentations. -/
theorem Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_presentation
    (M : (Spec R).Modules) (P : M.Presentation) (f : R) :
    IsLocalizedModule (Submonoid.powers f) (M.basicOpenRestriction f).hom := by
  letI := isIso_fromTildeΓ_of_presentation M P
  exact M.isLocalizedModule_basicOpenRestriction_of_isIso f

/-- **The affine comparison, as a characterisation.**

The counit is an isomorphism exactly when restriction to every basic open is a localisation.
Both directions are now available, so this is the statement to quote. -/
theorem Scheme.Modules.isIso_fromTildeΓ_iff_isLocalizedModule (M : (Spec R).Modules) :
    IsIso M.fromTildeΓ ↔
      ∀ f : R, IsLocalizedModule (Submonoid.powers f) (M.basicOpenRestriction f).hom :=
  ⟨fun _ f => M.isLocalizedModule_basicOpenRestriction_of_isIso f,
    isIso_fromTildeΓ_of_isLocalizedModule M⟩

end AlgebraicGeometry
