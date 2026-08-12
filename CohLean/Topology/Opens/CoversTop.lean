/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Sheaves.Over

/-!
# Covering the terminal object of an open-set site

`GrothendieckTopology.CoversTop` is the hypothesis every local-to-global statement on a site
takes. On the open-set site of a topological space it is implied by the far more familiar
condition that the family's supremum is `⊤`, and on `Spec R` that condition is in turn implied
by the purely algebraic one that the defining elements generate the unit ideal. This file
supplies both bridges.

## Main results

* `TopCat.Opens.grothendieckTopology_coversTop` — a family of opens with `⨆ i, U i = ⊤` covers
  the terminal object.
* `AlgebraicGeometry.basicOpen_coversTop_of_span_eq_top` — on `Spec R`, basic opens `D(gᵢ)`
  cover the terminal object as soon as `Ideal.span (Set.range g) = ⊤`.

## Why this is its own file

`grothendieckTopology_coversTop` previously lived in `CohLean/Coh/Descent/Locality.lean`. It is a statement
about topological spaces with no reference to coherence, sheaves of modules, or schemes, and its
position there made it unreachable from the lower-level topology and algebraic-geometry
infrastructure: those modules cannot import `Coh.Local` without creating a cycle.

That was a live constraint rather than an aesthetic one — the remaining half of the affine
comparison theorem (issue #46) needs `basicOpen_coversTop_of_span_eq_top` in
`AlgebraicGeometry/Modules/AffineComparison.lean`, which is exactly where the old placement
blocked it. Moving the lemma into the topology domain keeps the dependency direction explicit.

## Where the second one is used

Quasi-compactness of `Spec R` produces a *finite* subfamily of basic opens covering it, and
`PrimeSpectrum.iSup_basicOpen_eq_top_iff` turns that into `Ideal.span (Set.range g) = ⊤`. So the
shape a local-to-global argument actually has in hand is the algebraic condition, and
`basicOpen_coversTop_of_span_eq_top` is what converts it back into something the site machinery
(`SheafOfModules.IsFinitePresentation.of_coversTop`, `QuasicoherentData.coversTop`) accepts.

These declarations are maintained by CohLean. Their Mathlib-style namespaces express the
mathematical owner of the API and ease replacement by equivalent upstream declarations; they
do not imply any commitment to submit or merge them into Mathlib.
-/

universe u v

open CategoryTheory TopologicalSpace

namespace TopCat.Opens

variable {X : TopCat.{u}} {I : Type v}

/-- A family of open sets whose supremum is `⊤` covers the terminal object of the open-set
site. -/
lemma grothendieckTopology_coversTop
    (U : I → TopologicalSpace.Opens X) (hU : ⨆ i, U i = ⊤) :
    (_root_.Opens.grothendieckTopology X).CoversTop U := by
  intro V x hxV
  have hxTop : x ∈ (⊤ : TopologicalSpace.Opens X) := by simp
  rw [← hU, TopologicalSpace.Opens.mem_iSup] at hxTop
  obtain ⟨i, hxi⟩ := hxTop
  exact ⟨U i ⊓ V, homOfLE inf_le_right, ⟨i, ⟨homOfLE inf_le_left⟩⟩, hxi, hxV⟩

end TopCat.Opens

namespace TopCat.Presheaf

variable {X : TopCat.{u}} {B : Set (TopologicalSpace.Opens X)}
  {F G : Presheaf AddCommGrpCat.{u} X}

/-- A morphism of presheaves which is an isomorphism on an open basis becomes an isomorphism
after sheafification.

The basis members contained in an arbitrary open form a covering family. On those members the
map is both injective and surjective, which proves local bijectivity and hence membership in the
class inverted by sheafification. -/
theorem grothendieckTopology_W_of_isIso_app_of_isBasis
    (hB : TopologicalSpace.Opens.IsBasis B) (α : F ⟶ G)
    (hα : ∀ U ∈ B, IsIso (α.app (.op U))) :
    (_root_.Opens.grothendieckTopology X).W α := by
  let K := _root_.Opens.grothendieckTopology X
  have cover (U : TopologicalSpace.Opens X) :
      ⨆ i : { V : TopologicalSpace.Opens X // V ∈ B ∧ V ≤ U }, i.1 = U := by
    apply le_antisymm
    · exact iSup_le fun i ↦ i.2.2
    · intro x hx
      obtain ⟨V, hVB, hxV, hVU⟩ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.mp hB) hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hVB, hVU⟩, hxV⟩
  letI : CategoryTheory.Presheaf.IsLocallyInjective K α := by
    constructor
    intro U x y hxy
    let I := { V : TopologicalSpace.Opens X // V ∈ B ∧ V ≤ U.unop }
    let C : I → TopologicalSpace.Opens X := fun i ↦ i.1
    let R : Presieve U.unop :=
      TopCat.Presheaf.presieveOfCoveringAux C U.unop
    have hcover : Sieve.generate R ∈ K U.unop := by
      change Sieve.generate
          (TopCat.Presheaf.presieveOfCoveringAux C U.unop) ∈ K U.unop
      rw [← cover U.unop]
      exact TopCat.Presheaf.presieveOfCovering.mem_grothendieckTopology C
    apply K.superset_covering _ hcover
    rw [Sieve.generate_le_iff]
    intro V g hg
    obtain ⟨i, hi⟩ := hg
    subst V
    haveI := hα i.1 i.2.1
    apply (ConcreteCategory.isIso_iff_bijective (α.app (.op i.1))).mp inferInstance |>.1
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
  letI : CategoryTheory.Presheaf.IsLocallySurjective K α := by
    constructor
    intro U s
    let I := { V : TopologicalSpace.Opens X // V ∈ B ∧ V ≤ U }
    let C : I → TopologicalSpace.Opens X := fun i ↦ i.1
    let R : Presieve U := TopCat.Presheaf.presieveOfCoveringAux C U
    have hcover : Sieve.generate R ∈ K U := by
      change Sieve.generate
          (TopCat.Presheaf.presieveOfCoveringAux C U) ∈ K U
      rw [← cover U]
      exact TopCat.Presheaf.presieveOfCovering.mem_grothendieckTopology C
    apply K.superset_covering _ hcover
    rw [Sieve.generate_le_iff]
    intro V g hg
    obtain ⟨i, hi⟩ := hg
    subst V
    haveI := hα i.1 i.2.1
    obtain ⟨t, ht⟩ :=
      ((ConcreteCategory.isIso_iff_bijective (α.app (.op i.1))).mp inferInstance).2
        (G.map g.op s)
    exact ⟨t, ht⟩
  exact K.W_of_isLocallyBijective α

/-- A morphism on the slice site over `U` is inverted by sheafification when it is an
isomorphism on an open basis of the subspace `U`.

The statement uses `U.overEquivalence.inverse` to regard a subspace-open as an object over
`U`. This is the form needed by sheaves restricted to an open subset. -/
theorem grothendieckTopology_over_W_of_isIso_app_of_isBasis
    {U : TopologicalSpace.Opens X}
    {B : Set (TopologicalSpace.Opens U)}
    {F G : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    (hB : TopologicalSpace.Opens.IsBasis B) (α : F ⟶ G)
    (hα : ∀ V ∈ B,
      IsIso (α.app (.op (U.overEquivalence.inverse.obj V)))) :
    ((_root_.Opens.grothendieckTopology X).over U).W α := by
  rw [← ((_root_.Opens.grothendieckTopology X).over U).W_whiskerLeft_iff
    (K := _root_.Opens.grothendieckTopology U)
    (G := U.overEquivalence.inverse)]
  apply grothendieckTopology_W_of_isIso_app_of_isBasis
    (X := TopCat.of U) (B := B) hB
  intro V hV
  exact hα V hV

end TopCat.Presheaf

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}} {I : Type v}

/-- **Basic opens whose defining elements generate the unit ideal cover `Spec R`.**

This is the bridge from the algebraic side of quasi-compactness — a finite family with
`Ideal.span (Set.range g) = ⊤` — to the `CoversTop` hypothesis that the site machinery takes. -/
lemma basicOpen_coversTop_of_span_eq_top (g : I → R)
    (hg : Ideal.span (Set.range g) = ⊤) :
    (_root_.Opens.grothendieckTopology (Spec R)).CoversTop
      (fun i => PrimeSpectrum.basicOpen (g i)) :=
  TopCat.Opens.grothendieckTopology_coversTop _
    (PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hg)

end AlgebraicGeometry
