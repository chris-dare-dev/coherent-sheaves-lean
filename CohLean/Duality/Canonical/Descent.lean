/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.Duality.Canonical.Differentials
import CohLean.Topology.Opens.CoversTop

/-!
# Fixed-rank descent for the relative cotangent sheaf

This file isolates the genuinely sheaf-theoretic step in issue #119.  A family of local
trivializations by the free sheaf on `Fin n` canonically produces the repository's
`FiniteLocallyFreeData`.  For a smooth morphism of pure relative dimension `n`, Mathlib supplies
a standard-smooth affine chart around every point; `SmoothCotangentTrivializations` records only
the still-missing comparison which carries the affine Kähler calculation through sheafification.

Thus the global fixed-rank conclusion below is a theorem from explicit local comparisons, not a
new existence axiom.  Constructing those comparisons from smoothness alone, and descending the
top exterior power with its transition determinants, remain the two upstream-facing parts of
#119.
-/

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

/-- A cover on which a module sheaf is explicitly trivial of fixed rank `n`. -/
structure FixedRankTrivializations (E : X.Modules) (n : ℕ) where
  /-- Indexing type of the chosen cover. -/
  I : Type u
  /-- Opens in the trivializing cover. -/
  chartOpen : I → X.Opens
  /-- The chosen opens cover the scheme. -/
  coversTop : (_root_.Opens.grothendieckTopology X).CoversTop chartOpen
  /-- A rank-`n` free trivialization on every cover member. -/
  trivialization : ∀ i,
    SheafOfModules.free (R := X.ringCatSheaf.over (chartOpen i))
        (ULift.{u} (Fin n)) ≅
      E.over (chartOpen i)

namespace FixedRankTrivializations

variable {E : X.Modules} {n : ℕ}

/-- The local generating sections induced by the chosen free trivializations. -/
noncomputable def localGenerators (T : FixedRankTrivializations E n) :
    SheafOfModules.LocalGeneratorsData.{u}
      (show SheafOfModules X.ringCatSheaf from E) where
  I := T.I
  X := T.chartOpen
  coversTop := T.coversTop
  generators i :=
    { I := ULift.{u} (Fin n)
      s := (E.over (T.chartOpen i)).freeHomEquiv (T.trivialization i).hom
      epi := by
        rw [Equiv.symm_apply_apply]
        infer_instance }

/-- The induced local generators are bases rather than merely epimorphic generating families. -/
theorem localGenerators_isLocallyFreeData (T : FixedRankTrivializations E n) :
    T.localGenerators.IsLocallyFreeData := by
  constructor
  intro i
  change IsIso ((E.over (T.chartOpen i)).freeHomEquiv.symm
    ((E.over (T.chartOpen i)).freeHomEquiv (T.trivialization i).hom))
  rw [Equiv.symm_apply_apply]
  infer_instance

/-- Explicit rank-`n` trivializations produce fixed-rank locally-free data. -/
noncomputable def finiteLocallyFree (T : FixedRankTrivializations E n) :
    FiniteLocallyFreeData E n where
  localGenerators := T.localGenerators
  isLocallyFreeData := T.localGenerators_isLocallyFreeData
  rankEquiv _ := ⟨Equiv.ulift⟩

/-- In particular, an explicitly rank-`n`-trivialized sheaf is locally free. -/
theorem isLocallyFree (T : FixedRankTrivializations E n) :
    SheafOfModules.IsLocallyFree.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from E) :=
  T.finiteLocallyFree.isLocallyFree

end FixedRankTrivializations

end

end Scheme.Modules

namespace Variety

variable {k : Type u} [Field k] (X : Variety k)

/-- A standard-smooth affine chart of relative dimension `n` around a point. -/
structure SmoothChart (n : ℕ) (x : X.toScheme) where
  target : (Spec (CommRingCat.of k)).Opens
  targetAffine : IsAffineOpen target
  source : X.toScheme.Opens
  sourceAffine : IsAffineOpen source
  mem_source : x ∈ source
  source_le_preimage : source ≤ X.structureMorphism ⁻¹ᵁ target
  standardSmooth :
    RingHom.IsStandardSmoothOfRelativeDimension n
      (X.structureMorphism.appLE target source source_le_preimage).hom

namespace SmoothChart

/-- Choose the standard-smooth chart supplied at a point by smooth pure relative dimension. -/
noncomputable def ofSmooth {n : ℕ}
    (h : SmoothOfRelativeDimension n X.structureMorphism) (x : X.toScheme) :
    SmoothChart X n x :=
  Classical.choice (show Nonempty (SmoothChart X n x) from by
    obtain ⟨U, hU, V, hV, hx, e, hstd⟩ :=
      h.exists_isStandardSmoothOfRelativeDimension x
    exact ⟨
      { target := U
        targetAffine := hU
        source := V
        sourceAffine := hV
        mem_source := hx
        source_le_preimage := e
        standardSmooth := hstd }⟩)

end SmoothChart

/-- The missing sheafification comparison on the canonical standard-smooth chart cover.

The standard-smooth calculation proves that the objectwise Kähler module on every chosen chart
is free of rank `n`.  This structure asks precisely for the corresponding *sheaf* trivialization;
it does not ask again for a global locally-free atlas or determinant line. -/
structure SmoothCotangentTrivializations {n : ℕ}
    (h : SmoothOfRelativeDimension n X.structureMorphism) where
  trivialization : ∀ x : X.toScheme,
    SheafOfModules.free
        (R := X.toScheme.ringCatSheaf.over ((SmoothChart.ofSmooth X h x).source))
        (ULift.{u} (Fin n)) ≅
      (relativeDifferentials X).over ((SmoothChart.ofSmooth X h x).source)

namespace SmoothCotangentTrivializations

variable {X} {n : ℕ} {h : SmoothOfRelativeDimension n X.structureMorphism}

/-- The source opens of the chosen smooth charts cover the variety. -/
theorem chartSources_coversTop (_T : SmoothCotangentTrivializations X h) :
    (_root_.Opens.grothendieckTopology X.toScheme).CoversTop
      (fun x : X.toScheme ↦ (SmoothChart.ofSmooth X h x).source) := by
  rw [_root_.Opens.coversTop_iff]
  apply top_unique
  intro x _hx
  exact Opens.mem_iSup.mpr
    ⟨x, (SmoothChart.ofSmooth X h x).mem_source⟩

/-- Package the smooth-chart comparisons as fixed-rank trivializations of `Ω¹_{X/k}`. -/
noncomputable def fixedRankTrivializations (T : SmoothCotangentTrivializations X h) :
    Scheme.Modules.FixedRankTrivializations (relativeDifferentials X) n where
  I := X.toScheme
  chartOpen x := (SmoothChart.ofSmooth X h x).source
  coversTop := T.chartSources_coversTop
  trivialization := T.trivialization

/-- The chartwise sheafification comparisons globalize to fixed-rank locally-free cotangent
data. -/
noncomputable def finiteLocallyFree (T : SmoothCotangentTrivializations X h) :
    Scheme.Modules.FiniteLocallyFreeData (relativeDifferentials X) n :=
  T.fixedRankTrivializations.finiteLocallyFree

/-- The constructed relative cotangent sheaf is locally free once the chart comparisons are
supplied. -/
theorem relativeDifferentials_isLocallyFree (T : SmoothCotangentTrivializations X h) :
    SheafOfModules.IsLocallyFree.{u, u, u}
      (show SheafOfModules X.toScheme.ringCatSheaf from relativeDifferentials X) :=
  T.finiteLocallyFree.isLocallyFree

end SmoothCotangentTrivializations

end Variety

end AlgebraicGeometry
