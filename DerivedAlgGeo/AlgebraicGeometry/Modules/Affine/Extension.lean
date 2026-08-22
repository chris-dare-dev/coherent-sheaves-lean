/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Clearing a denominator on an affine

A section of a quasi-coherent sheaf over a basic open `D(r)`, multiplied by a high enough power of
`r`, is the restriction of a **global** section. This is the chart-local engine of `#585`: on
`Proj 𝒜` a degree-one chart is `Spec (A_{(g)})`, `D₊(f)` meets it in the basic open of `f / g`
(`Proj.awayι_preimage_basicOpen`), and this is what clears that denominator.

## Why it is six lines, and what that changes

Not by an argument but by an instance. Mathlib carries

    instance (f : R) : IsLocalizedModule.Away f (tilde.toOpen M (basicOpen f)).hom

so `Γ(D(r), M~)` **is** the localization `M_r`, and clearing the denominator is
`IsLocalizedModule.surj`: a section is `m / rⁿ` by the definition of the localization rather than
by a theorem about it. The passage from "comes from `M`" to "restricts from a *global* section" is
then `tilde.toOpen_res`, which is `rfl`.

Worth recording against the plan `#585` was written to.
`Submodule.exists_pow_smul_mem_of_isLocalized_radical` — extracted into
`Algebra/Module/LocalizedRadical.lean` for this very issue — is **not** needed here. It stays the
tool for reconciling two charts on their overlap, where the denominators come from a cover and
radical membership is what makes the cover a cover. The chart-local step never reaches for it.

## Dropping the tilde hypothesis

`exists_pow_smul_eq_res_of_top_of_isQuasicoherent` is the statement `#585` actually consumes: `N`
is any quasi-coherent module sheaf on `Spec R`, not a tilde. It is the tilde case transported
across `fromTildeΓ`, which quasi-coherence makes an isomorphism.

Four of that proof's six lines are spelling rather than mathematics, and each cost a cycle:

* `modulesSpecToSheaf` lands in an **induced** category, so `e.hom.val` does not project — the
  natural transformation has to be reached through `TopCat.Sheaf.forget` instead;
* `(modulesSpecToSheaf.obj N).presheaf.map` and `((modulesSpecToSheaf ⋙ forget).obj N).map` are the
  same map in two spellings, and `rw` matches syntactically, so both the goal and the hypothesis
  must be restated before naturality will fire;
* inside `namespace AlgebraicGeometry.Scheme.Modules`, `map_smul` resolves to a *different* lemma,
  about `presheaf.map`. It has to be written `_root_.map_smul`. Same class of hazard as
  `references/instance-transparency.md`: a name that silently resolves to the wrong thing.

## Scope

One affine, one basic open. The `Proj` chart application, the choice of one `n` across a finite
cover, and the passage from `(f / g)ⁿ ·` to multiplication into the twist `F(n)` are not here, so
`#585` is not closed.
-/

universe u

open CategoryTheory Opposite TopologicalSpace PrimeSpectrum

namespace AlgebraicGeometry.tilde

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- **A section of `M~` over a basic open extends after clearing one power of the defining
element.** -/
theorem exists_pow_smul_eq_toOpen (r : R)
    (s : (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op (basicOpen r))) :
    ∃ (n : ℕ) (m : M), r ^ n • s = toOpen M (basicOpen r) m := by
  obtain ⟨⟨m, t⟩, ht⟩ :=
    IsLocalizedModule.surj (Submonoid.powers r) (toOpen M (basicOpen r)).hom s
  obtain ⟨n, hn⟩ := t.2
  exact ⟨n, m, by rw [show r ^ n = (t : R) from hn]; exact ht⟩

/-- **The same, as an extension statement**: a power of `r` times a section over `D(r)` is the
restriction of a *global* section. -/
theorem exists_pow_smul_eq_res_of_top (r : R)
    (s : (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op (basicOpen r))) :
    ∃ (n : ℕ) (t : (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op ⊤)),
      (modulesSpecToSheaf.obj (tilde M)).presheaf.map (homOfLE le_top).op t = r ^ n • s := by
  obtain ⟨n, m, hm⟩ := exists_pow_smul_eq_toOpen M r s
  refine ⟨n, toOpen M ⊤ m, ?_⟩
  rw [hm]
  rfl

end AlgebraicGeometry.tilde

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- **The same for any quasi-coherent module sheaf on an affine**, not only a tilde. -/
theorem exists_pow_smul_eq_res_of_top_of_isQuasicoherent (N : (Spec R).Modules)
    [IsIso (fromTildeΓ N)] (r : R)
    (s : (modulesSpecToSheaf.obj N).presheaf.obj (op (PrimeSpectrum.basicOpen r))) :
    ∃ (n : ℕ) (t : (modulesSpecToSheaf.obj N).presheaf.obj (op ⊤)),
      (modulesSpecToSheaf.obj N).presheaf.map (homOfLE le_top).op t = r ^ n • s := by
  let e := (modulesSpecToSheaf ⋙ TopCat.Sheaf.forget (ModuleCat R) (Spec R)).mapIso
    (asIso (fromTildeΓ N))
  obtain ⟨n, t', ht'⟩ :=
    AlgebraicGeometry.tilde.exists_pow_smul_eq_res_of_top _ r
      (e.inv.app (op (PrimeSpectrum.basicOpen r)) s)
  replace ht' : (((modulesSpecToSheaf ⋙ TopCat.Sheaf.forget (ModuleCat R) (Spec R)).obj
      (tilde ((modulesSpecToSheaf.obj N).presheaf.obj (op ⊤)))).map (homOfLE le_top).op) t' =
        r ^ n • e.inv.app (op (PrimeSpectrum.basicOpen r)) s := ht'
  refine ⟨n, e.hom.app (op ⊤) t', ?_⟩
  show (((modulesSpecToSheaf ⋙ TopCat.Sheaf.forget (ModuleCat R) (Spec R)).obj N).map
    (homOfLE le_top).op) (e.hom.app (op ⊤) t') = _
  rw [← NatTrans.naturality_apply e.hom (homOfLE le_top).op t', ht', _root_.map_smul]
  congr 1
  exact (e.app (op (PrimeSpectrum.basicOpen r))).inv_hom_id_apply s

end AlgebraicGeometry.Scheme.Modules
