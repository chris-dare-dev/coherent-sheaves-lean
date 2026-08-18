/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Sets.Opens

/-!
# Irreducibility from a cover by pairwise-meeting irreducible opens

A space covered by preirreducible opens that pairwise intersect is preirreducible. This is the
form the projective spectrum needs: `Proj 𝒜` of a graded domain is covered by the basic opens
`D₊(f)`, each the spectrum of a domain and so irreducible, and any two of them meet because the
product of two nonzero homogeneous elements is nonzero.

Mathlib has the irreducibility of `Spec` of a domain and the local-to-global machinery for
schemes, but not this purely topological step.
-/

open Set TopologicalSpace

namespace TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- A cover by preirreducible open sets that pairwise intersect makes the whole space
preirreducible. -/
theorem isPreirreducible_univ_of_cover {ind : Type*} (U : ind → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hirred : ∀ i, IsPreirreducible (U i))
    (hmeet : ∀ i j, (U i ∩ U j).Nonempty) :
    IsPreirreducible (Set.univ : Set X) := by
  intro V W hV hW hVne hWne
  obtain ⟨v, -, hvV⟩ := hVne
  obtain ⟨w, -, hwW⟩ := hWne
  obtain ⟨i, hi⟩ := hcover v
  obtain ⟨j, hj⟩ := hcover w
  -- inside `U i`, the open `V` meets `U j`
  obtain ⟨p, hpUi, hpV, hpUj⟩ :=
    hirred i V (U j) hV (hopen j) ⟨v, hi, hvV⟩ (hmeet i j)
  -- inside `U j`, the open `V ∩ U i` meets `W`
  obtain ⟨q, hqUj, ⟨hqV, -⟩, hqW⟩ :=
    hirred j (V ∩ U i) W (hV.inter (hopen i)) hW ⟨p, hpUj, hpV, hpUi⟩ ⟨w, hj, hwW⟩
  exact ⟨q, mem_univ q, hqV, hqW⟩

/-- A nonempty space covered by preirreducible open sets that pairwise intersect is an
irreducible space. -/
theorem irreducibleSpace_of_cover {ind : Type*} [Nonempty X] (U : ind → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hirred : ∀ i, IsPreirreducible (U i))
    (hmeet : ∀ i j, (U i ∩ U j).Nonempty) :
    IrreducibleSpace X where
  toPreirreducibleSpace :=
    ⟨isPreirreducible_univ_of_cover U hopen hcover hirred hmeet⟩
  toNonempty := ‹_›

end TopologicalSpace
