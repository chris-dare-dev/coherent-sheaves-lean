/-
Nonvacuity check for the independent review of PR #76 (issue #86).

`HeartTorsionPair` is inhabited for **every** t-structure: the degenerate
torsion pair whose torsion class is the whole heart and whose torsion-free
class is the zero objects. Its tilt therefore exists whenever `C` is
triangulated, and its co-aisle is the original one at every level — the
orthogonality clause is vacuous because every map into a zero object is zero.

Elaborate from the repo root with:

  lake env lean scratch/TiltNonvacuity.lean
-/
import BridgelandStabLean.Tilting.HeartTorsionPair

namespace BridgelandStabLean.Tilting.Review86

open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated ZeroObject

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

variable (t : TStructure C)

/-- The degenerate torsion pair on the heart of `t`: everything in the heart is
torsion, only zero objects are torsion-free. The decomposition triangle is the
contractible one. -/
def trivialPair : HeartTorsionPair t where
  tors X := t.IsLE X 0 ∧ t.IsGE X 0
  free X := IsZero X
  tors_isLE _ h := h.1
  tors_isGE _ h := h.2
  free_isLE _ h := t.isLE_of_isZero h 0
  free_isGE _ h := t.isGE_of_isZero h 0
  tors_isClosedUnderIsomorphisms :=
    ⟨fun {X Y} e h => by
      haveI := h.1
      haveI := h.2
      exact ⟨t.isLE_of_iso e 0, t.isGE_of_iso e 0⟩⟩
  free_isClosedUnderIsomorphisms := ⟨fun {X Y} e h => h.of_iso e.symm⟩
  hom_eq_zero := fun _ Y _ hY f => hY.eq_of_tgt f 0
  exists_triangle X hle hge :=
    ⟨X, 0, ⟨hle, hge⟩, isZero_zero C, 𝟙 X, 0, 0, contractible_distinguished X⟩

/-- The tilt of the degenerate pair exists: `HeartTorsionPair.tilt` is
nonvacuous for every t-structure on every triangulated category. -/
noncomputable example [IsTriangulated C] : TStructure C := (trivialPair t).tilt

/-- Indexing sanity check, no octahedra involved: the tilted co-aisle of the
degenerate pair is the original co-aisle at every integer level. -/
theorem trivialPair_tiltLEAt (n : ℤ) (X : C) :
    (trivialPair t).tiltLEAt n X ↔ t.le n X := by
  constructor
  · rintro ⟨hle, -⟩
    exact hle.le
  · intro h
    exact ⟨⟨h⟩, fun F hF f => hF.eq_of_tgt f 0⟩

/-- The same statement read off the assembled `TStructure` itself, through the
`tilt_le` computation lemma. -/
theorem trivialPair_tilt_le [IsTriangulated C] (n : ℤ) (X : C) :
    (trivialPair t).tilt.le n X ↔ t.le n X := by
  rw [HeartTorsionPair.tilt_le]
  exact trivialPair_tiltLEAt t n X

end BridgelandStabLean.Tilting.Review86
