/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.StabilityFunction.Uniqueness.Extrema

/-!
# The two classes at a phase cutoff

Bridgeland's torsion pair is cut from `Coh X` by a slope, and #709 turned the
slope order into the phase order, so the cut is by a phase. This file defines
the two classes and proves what follows from the Harder–Narasimhan machinery
already in `Uniqueness/`:

```
T β = {E | every HN phase of E exceeds β}      F β = {E | every HN phase is at most β}
```

* `mem_hnTors_iff_forall`, `mem_hnFree_iff_forall` — the classes are
  well defined: `φ⁻` and `φ⁺` are intrinsic (`phiMinus_eq`, `phiPlus_eq`), so
  "some filtration" and "every filtration" agree. The HN property is a
  hypothesis of these two and of nothing else: without a filtration to exhibit,
  the universally quantified form is vacuous while membership asks for a
  witness.
* `isZero_of_mem_hnTors_of_mem_hnFree` — the two classes meet only in zero,
  which is `φ⁻ ≤ φ⁺` and nothing else.
* `hom_eq_zero_of_mem_hnTors_of_semistable` — **the Hom-vanishing, for a
  semistable target.**

## What is deliberately not here

Two further steps stand between this and a torsion pair, and neither is implied
by anything below.

* **Hom-vanishing for a general target.** The argument is the usual one — the
  image of a map is a quotient of the source and a subobject of the target, so
  `β < φ⁻(image) ≤ φ⁺(image) ≤ β` — but it needs `φ⁺` to decrease under monos
  and `φ⁻` to increase under epis, and the tree has neither. `Uniqueness/` has
  the semistable special cases and the maximal destabilizing subobject; it does
  not have these.
* **The splitting.** Every object sitting in a short exact sequence with a
  torsion sub and a torsion-free quotient, obtained by cutting the HN chain at
  the crossing index. `Uniqueness/Tail.lean` removes one factor at a time and is
  the machinery this would induct over.

Until both exist, these are two classes with a Hom-vanishing property, not a
torsion pair, and nothing here calls them one.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace StabilityFunction

variable (Z : StabilityFunction A) (β : ℝ)

/-- The **torsion class** at a cutoff: the zero object, and the objects whose
Harder–Narasimhan phases all exceed `β`. -/
def hnTors : Set A :=
  {E | IsZero E ∨ ∃ F : AbelianHNFiltration Z E, β < F.phiMinus}

/-- The **torsion-free class** at a cutoff: the zero object, and the objects
whose Harder–Narasimhan phases are all at most `β`. -/
def hnFree : Set A :=
  {E | IsZero E ∨ ∃ F : AbelianHNFiltration Z E, F.phiPlus ≤ β}

variable {Z β}

theorem isZero_mem_hnTors {E : A} (hE : IsZero E) : E ∈ hnTors Z β := Or.inl hE

theorem isZero_mem_hnFree {E : A} (hE : IsZero E) : E ∈ hnFree Z β := Or.inl hE

/-- Membership is independent of the filtration chosen, because `φ⁻` is.

The HN property is needed for the reverse direction only: without a filtration
to exhibit, the universally quantified condition is vacuous while membership
asks for a witness. -/
theorem mem_hnTors_iff_forall (hHN : Z.HasHNProperty) {E : A} (hE : ¬IsZero E) :
    E ∈ hnTors Z β ↔ ∀ F : AbelianHNFiltration Z E, β < F.phiMinus := by
  obtain ⟨G⟩ := hHN E hE
  constructor
  · rintro (h | ⟨F, hF⟩) K
    · exact absurd h hE
    · rwa [AbelianHNFiltration.phiMinus_eq K F]
  · exact fun h => Or.inr ⟨G, h G⟩

/-- Membership is independent of the filtration chosen, because `φ⁺` is. -/
theorem mem_hnFree_iff_forall (hHN : Z.HasHNProperty) {E : A} (hE : ¬IsZero E) :
    E ∈ hnFree Z β ↔ ∀ F : AbelianHNFiltration Z E, F.phiPlus ≤ β := by
  obtain ⟨G⟩ := hHN E hE
  constructor
  · rintro (h | ⟨F, hF⟩) K
    · exact absurd h hE
    · rwa [AbelianHNFiltration.phiPlus_eq K F]
  · exact fun h => Or.inr ⟨G, h G⟩

/-- **The two classes meet only in zero.** An object in both would have
`β < φ⁻ ≤ φ⁺ ≤ β`. -/
theorem isZero_of_mem_hnTors_of_mem_hnFree {E : A}
    (hT : E ∈ hnTors Z β) (hF : E ∈ hnFree Z β) : IsZero E := by
  by_contra hE
  obtain ⟨F, hmin⟩ : ∃ F : AbelianHNFiltration Z E, β < F.phiMinus := by
    rcases hT with h0 | h; · exact absurd h0 hE
    · exact h
  obtain ⟨K, hmax⟩ : ∃ K : AbelianHNFiltration Z E, K.phiPlus ≤ β := by
    rcases hF with h0 | h; · exact absurd h0 hE
    · exact h
  have hKF : K.phiPlus = F.phiPlus := AbelianHNFiltration.phiPlus_eq K F
  have := F.phiMinus_le_phiPlus
  rw [hKF] at hmax
  linarith

/-- **Hom-vanishing, for a semistable target.** A map from an object whose HN
phases all exceed `β` to a semistable object of phase at most `β` is zero. -/
theorem hom_eq_zero_of_mem_hnTors_of_semistable {E B : A}
    (hE : ¬IsZero E) (hT : E ∈ hnTors Z β) (hB : Z.IsSemistable B)
    (hphase : Z.phase B ≤ β) (f : E ⟶ B) : f = 0 := by
  obtain ⟨F, hmin⟩ : ∃ F : AbelianHNFiltration Z E, β < F.phiMinus := by
    rcases hT with h0 | h; · exact absurd h0 hE
    · exact h
  exact AbelianHNFiltration.hom_eq_zero_to_semistable_of_phase_lt_phiMinus F hB
    (by linarith) f

end StabilityFunction

end CategoryTheory.Triangulated
