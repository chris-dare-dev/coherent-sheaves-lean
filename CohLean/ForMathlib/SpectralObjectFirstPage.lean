/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import CohLean.ForMathlib.SpectralObjectSpectralSequence

/-!
# The first page of the spectral sequence of a spectral object

This file backports the first-page computation API for spectral objects.  If the four filtration
indices defining the initial page occur in equal pairs, its objects are values of the homological
functor `X.H`, and its differential is the connecting morphism `X.δ`.
-/

namespace CategoryTheory

open Category ComposableArrows

namespace Abelian.SpectralObject

variable {C ι κ : Type*} [Category C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (data : SpectralSequenceDataCore ι c r₀)

namespace SpectralSequenceDataCore

/-- The initial-page indices occur in equal pairs, so its objects can be expressed using `X.H`. -/
class HasFirstPageComputation : Prop where
  hi₀₁ (pq : κ) : data.i₀ r₀ pq = data.i₁ pq
  hi₂₃ (pq : κ) : data.i₂ pq = data.i₃ r₀ pq

export HasFirstPageComputation (hi₀₁ hi₂₃)

instance : coreE₂Cohomological.HasFirstPageComputation where
  hi₀₁ pq := by dsimp; lia
  hi₂₃ pq := by dsimp; lia

instance : coreE₂CohomologicalNat.HasFirstPageComputation where
  hi₀₁ pq := by dsimp; lia
  hi₂₃ pq := by dsimp; lia

instance : coreE₂HomologicalNat.HasFirstPageComputation where
  hi₀₁ pq := by dsimp; lia
  hi₂₃ pq := by dsimp; lia

end SpectralSequenceDataCore

variable [data.HasFirstPageComputation] [X.HasSpectralSequence data]

/-- Identify an object on the initial page with the homological functor applied to the
corresponding adjacent filtration quotient. -/
noncomputable def spectralSequenceFirstPageXIso (pq : κ)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n : ℤ) (hn : n = data.deg pq) :
    ((X.spectralSequence data).page r₀).X pq ≅
      (X.H n).obj (mk₁ (homOfLE (data.le₁₂' pq hi₁ hi₂))) :=
  X.spectralSequencePageXIso data _ (by rfl) _ _ _ _ _
    (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃]) _ _ _ hn ≪≫
      X.EIsoH (homOfLE _) (n - 1) n (n + 1)

@[reassoc]
lemma spectralSequenceFirstPageXIso_hom (pq : κ)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n₀ n₁ n₂ : ℤ) (hn₁' : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.spectralSequenceFirstPageXIso data pq i₁ i₂ hi₁ hi₂ n₁ hn₁').hom =
      (X.spectralSequencePageXIso data r₀ (by rfl) _ _ _ _ _
        (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃]) _ _ _ hn₁').hom ≫
          (X.EIsoH _ n₀ n₁ n₂ hn₁ hn₂).hom := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  obtain rfl := hn₂
  rfl

@[reassoc]
lemma spectralSequenceFirstPageXIso_inv (pq : κ)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n₀ n₁ n₂ : ℤ) (hn₁' : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.spectralSequenceFirstPageXIso data pq i₁ i₂ hi₁ hi₂ n₁ hn₁').inv =
      (X.EIsoH _ n₀ n₁ n₂ hn₁ hn₂).inv ≫
      (X.spectralSequencePageXIso data r₀ (by rfl) _ _ _ _ _
        (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃]) _ _ _ hn₁').inv := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  obtain rfl := hn₂
  rfl

/-- Under the initial-page identifications, its differential is the connecting morphism `X.δ`. -/
@[reassoc]
lemma spectralSequence_first_page_d_eq (pq pq' : κ)
    (hpq : (c r₀).Rel pq pq') (i j k : ι)
    (hi : i = data.i₁ pq') (hj : j = data.i₁ pq) (hk : k = data.i₂ pq)
    (n n' : ℤ) (hn : n = data.deg pq) (hn' : n + 1 = n' := by lia) :
    ((X.spectralSequence data).page r₀).d pq pq' =
      (X.spectralSequenceFirstPageXIso data pq j k hj hk n hn).hom ≫
      X.δ
        (homOfLE
          (by simpa only [hi, hj, data.hc₁₃ r₀ pq pq' hpq, ← data.hi₂₃ pq']
            using data.le₁₂ pq'))
        (homOfLE (by simpa only [hj, hk] using data.le₁₂ pq)) n n' hn' ≫
      (X.spectralSequenceFirstPageXIso data pq' i j hi
        (by rw [hj, ← data.hc₀₂ r₀ pq pq' hpq, data.hi₀₁ pq]) n'
        (by rw [← hn', hn, data.hc r₀ pq pq' hpq])).inv := by
  simpa [X.spectralSequenceFirstPageXIso_hom data pq j k hj hk (n - 1) n n',
    ← X.d_EIsoH_hom_assoc _ _ (n - 1) n n' (n' + 1),
    X.spectralSequenceFirstPageXIso_inv data pq' i j hi _ _ n' _ _ hn' _]
    using spectralSequence_page_d_eq _ _ _ _ _ _ hpq ..

end Abelian.SpectralObject

end CategoryTheory
