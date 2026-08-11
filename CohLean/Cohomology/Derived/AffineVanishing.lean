/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.AlgebraicGeometry.Modules.Affine.Equivalence
import CohLean.Cohomology.Cech.Affine
import CohLean.Cohomology.Cech.GlobalComparison

/-!
# The affine derived-vanishing boundary

The explicit affine calculation proves that the module-valued Čech complex of `M~` on a finite
standard distinguished-open cover is exact in every positive degree. This file transfers that
calculation to Mathlib's derived cohomology `Sheaf.H` once a comparison with that explicit complex
is supplied. It also transports the result across the affine module-sheaf equivalence.

There is deliberately no unconditional affine derived-vanishing theorem here yet. The comparison
theorem for a single Čech-acyclic cover cannot supply it without circularity: its hypothesis already
asserts derived vanishing on all finite intersections. The missing input is the basis/cofinal-cover
criterion used by Stacks Project, Lemma 20.11.9 (Tag 01EW). Keeping the comparison below as a visible
proposition records that boundary without adding an axiom or overstating the current library.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Cohomology

/-- The underlying abelian sheaf of the module sheaf associated to an affine module. This is the
object to which Mathlib's `Sheaf.H` applies. -/
noncomputable abbrev underlyingTildeSheaf {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :=
  (Scheme.Modules.toSheaf (Spec R)).obj (tilde M)

/-- The explicit module-valued Čech complex used by the affine localization calculation. -/
noncomputable abbrev affineTildeCechComplex
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (M : ModuleCat.{u} R) :=
  (cechComplexFunctor fun i ↦ _root_.PrimeSpectrum.basicOpen (f i)).obj
    (modulesSpecToSheaf.obj (tilde M)).presheaf

/-- The exact comparison input still needed to turn the explicit module-valued affine Čech
calculation into derived cohomology in degree `k`.

The intended construction is the basis/cofinal-cover argument of Stacks Tag 01EW. It is stronger
than merely assuming that one particular cover is already Leray-acyclic. -/
def AffineTildeCechDerivedComparisonAt
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (M : ModuleCat.{u} R) (k : ℕ)
    [HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})] : Prop :=
  Nonempty (((affineTildeCechComplex f M).homology k : ModuleCat.{u} R) ≃+
    (underlyingTildeSheaf M).H k)

/-- Degreewise comparison between the explicit affine Čech complex and derived cohomology. -/
def AffineTildeCechDerivedComparison
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (M : ModuleCat.{u} R)
    [HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})] : Prop :=
  ∀ k, AffineTildeCechDerivedComparisonAt f M k

/-- Positive exactness of the standard affine Čech complex kills `Sheaf.H` once the comparison
with that explicit complex is available. -/
theorem tilde_H_subsingleton_of_comparisonAt
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (M : ModuleCat.{u} R) (k : ℕ) (hk : 0 < k)
    [HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})]
    (hcomparison : AffineTildeCechDerivedComparisonAt f M k) :
    Subsingleton ((underlyingTildeSheaf M).H k) := by
  have hexact : (affineTildeCechComplex f M).ExactAt k :=
    tilde_cechComplex_exactAt_of_pos f hf M k hk
  have hzero : IsZero ((affineTildeCechComplex f M).homology k) :=
    hexact.isZero_homology
  letI : Subsingleton
      ((affineTildeCechComplex f M).homology k : ModuleCat.{u} R) :=
    ModuleCat.subsingleton_of_isZero hzero
  let e := hcomparison.some
  exact ⟨fun x y ↦ e.symm.injective (Subsingleton.elim _ _)⟩

/-- All-degree comparison gives affine derived vanishing in every positive degree. -/
theorem tilde_H_subsingleton_of_comparison
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (M : ModuleCat.{u} R)
    [HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})]
    (hcomparison : AffineTildeCechDerivedComparison f M)
    (k : ℕ) (hk : 0 < k) : Subsingleton ((underlyingTildeSheaf M).H k) :=
  tilde_H_subsingleton_of_comparisonAt f hf M k hk (hcomparison k)

/-- Derived vanishing transports across an isomorphism of underlying abelian sheaves. -/
theorem H_subsingleton_of_iso_tilde
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (M : ModuleCat.{u} R)
    (F : Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})
    (e : F ≅ underlyingTildeSheaf M) (k : ℕ) (hk : 0 < k)
    [HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})]
    (hcomparison : AffineTildeCechDerivedComparisonAt f M k) :
    Subsingleton (F.H k) := by
  have hsub : Subsingleton ((underlyingTildeSheaf M).H k) :=
    tilde_H_subsingleton_of_comparisonAt f hf M k hk hcomparison
  let eH := (Sheaf.functorH (Opens.grothendieckTopology (Spec R)) k).mapIso e
  let eA := eH.addCommGroupIsoToAddEquiv
  exact ⟨fun x y ↦ eA.injective (hsub.elim _ _)⟩

/-- Quasi-coherent module sheaves identified with `M~` inherit the same positive-degree
vanishing statement. This is the form directly consumed by the affine equivalence from B1. -/
theorem modules_H_subsingleton_of_iso_tilde
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (M : ModuleCat.{u} R) (G : (Spec R).Modules) (e : G ≅ tilde M)
    (k : ℕ) (hk : 0 < k)
    [HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})]
    (hcomparison : AffineTildeCechDerivedComparisonAt f M k) :
    Subsingleton (((Scheme.Modules.toSheaf (Spec R)).obj G).H k) :=
  H_subsingleton_of_iso_tilde f hf M _
    ((Scheme.Modules.toSheaf (Spec R)).mapIso e) k hk hcomparison

end AlgebraicGeometry.Cohomology
