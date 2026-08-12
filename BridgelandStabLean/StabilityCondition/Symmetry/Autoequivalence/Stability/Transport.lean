/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.StabilityCondition.Symmetry.Autoequivalence.Foundations.FiniteLength
import BridgelandStability.Deformation.IntervalSelection
import MathFormalContract

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Transporting stability conditions by autoequivalences

The assembly step. `G̃L⁺(2, ℝ)` moves phases and fixes objects; an
autoequivalence does the opposite, and this file carries it all the way to
`StabilityCondition.WithClassMap`.

Three things had to line up, and each is the *dual* of the corresponding step
in the `G̃L⁺(2, ℝ)` track:

* **Slicing** — `Slicing.mapEquiv` (`StabilityCondition/Symmetry/Autoequivalence/Slicing/Transport.lean`), dual to `relabel`.
* **Local finiteness** — `mapEquiv_isLocallyFinite` below. Dual to
  `relabel_isLocallyFinite`, but *easier*: the interval endpoints do not move
  (`mapEquiv_intervalProp_iff`), so the **same `η` works** and no
  uniform-continuity argument is needed. What is needed instead is that `Φ⁻¹`
  restricts to a full faithful strict-mono-preserving functor between the two
  interval categories.
* **Central charge** — `actStabAut` below, via a class-lattice datum `lam`.

## How strict monos survive `Φ⁻¹`

`autFunctor_strictMono` uses the **cone route**, not the heart route: take a
strict mono's cokernel triangle
(`interval_strictShortExact_cokernel_of_strictMono` then
`exists_distTriang_of_strictShortExact`), push it through `Φ⁻¹` — which is
triangulated, so the triangle stays distinguished and all three vertices stay
in the *same* window — then read the strict mono back off with
`strictMono_strictEpi_of_distTriang`. This is exactly how the foundational library's own
`intervalInclusion_map_strictMono` works.

The heart route would not have worked: `toRightHeart` lands in the heart of
`phaseShift C (b - 1)`, and the two slicings' hearts are different
subcategories of `C`.

## The class-lattice datum

An autoequivalence acts on `WithClassMap C v` only *together with* a
`lam : Λ →+ Λ` satisfying `v ∘ K₀.mapF Φ⁻¹ = lam ∘ v`. That is not a
technicality — `v` is arbitrary, and nothing forces `Φ` to respect it. When
`v = id` the datum is forced (`lam = K₀.mapF Φ⁻¹`); in general it is extra
input, structurally exactly as `Compatible` is for `GLTilde`.

With it, `compat'` costs nothing: the witness `m` is *unchanged*, because `Φ`
moves the object but not its phase. Contrast the `G̃L⁺(2, ℝ)` case, where the
matrix rescales the ray and `m` becomes `m * r`.

## What this is NOT — and what became of that

This file gives the action as a well-defined **map** plus its defining
property, not a group action. The acting object is a *pair* `(Φ, lam)`, and
`AutQuot` groups the `Φ`s alone — enough for slicings, not once a class lattice
is in play.

`StabilityCondition/Symmetry/Autoequivalence/Stability/ClassMap.lean` bundles the pair and supplies the `MulAction`. **Nothing
here is superseded by it**, and the split is worth keeping: that file needs
`lam : Λ ≃+ Λ`, because a group needs `lam⁻¹` and nothing produces one, while
`actStabAut` below asks only for `lam : Λ →+ Λ`. A non-invertible compatible
datum still acts as a map and is simply not a member of that group, so this
statement is strictly the more general of the two.

See `notes/dependencies/BridgelandStabilityAPI.md` §7.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Triangulated

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

variable (Φ : C ≌ C)
  [Φ.functor.Additive] [Φ.inverse.Additive]
  [Φ.functor.CommShift ℤ] [Φ.inverse.CommShift ℤ]
  [Φ.functor.IsTriangulated] [Φ.inverse.IsTriangulated]

/-! ## `Φ⁻¹` between interval categories -/

/-- `Φ⁻¹` restricted to interval subcategories. The endpoints are unchanged —
that is `mapEquiv_intervalProp_iff`.

An `abbrev` deliberately: instance search must see through it to find the
`Full`/`Faithful` instances of the underlying `ObjectProperty.lift`. -/
abbrev autIntervalFunctor (s : Slicing C) (a b : ℝ) :
    (s.mapEquiv Φ).IntervalCat C a b ⥤ s.IntervalCat C a b :=
  (s.intervalProp C a b).lift
    (((s.mapEquiv Φ).intervalProp C a b).ι ⋙ Φ.inverse)
    (fun X => (mapEquiv_intervalProp_iff Φ s a b X.obj).mp X.property)

/-- Strict monos survive `Φ⁻¹`, by the cone route. -/
theorem autFunctor_strictMono (s : Slicing C) (a b : ℝ)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : (s.mapEquiv Φ).IntervalCat C a b} (f : X ⟶ Y) (hf : IsStrictMono f) :
    IsStrictMono ((autIntervalFunctor Φ s a b).map f) := by
  have hsse := interval_strictShortExact_cokernel_of_strictMono (C := C) f hf
  obtain ⟨δ, hδ⟩ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
    (C := C) (s.mapEquiv Φ) hsse
  exact (Slicing.IntervalCat.strictMono_strictEpi_of_distTriang (C := C) s
    (S := (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).map
      (autIntervalFunctor Φ s a b))
    (δ := Φ.inverse.map δ ≫ (Φ.inverse.commShiftIso (1 : ℤ)).hom.app _)
    (by simpa using Φ.inverse.map_distinguished _ hδ)).1

/-! ## Local finiteness -/

/-- **Local finiteness survives an autoequivalence, with the SAME radius.**

Dual to `relabel_isLocallyFinite` and strictly easier: the windows do not move,
so `exists_radius` is not needed. The content is instead the strict-finite-length
transfer along `Φ⁻¹`. -/
@[cites "stmt:a520a8d4f877:bridgeland2007.def-5.7" (relation := no_claim)
        (note := "Bound to the locally-finite DEFINITION because this theorem is what preserves it, not what states it. no_claim is the honest relation: a transport result neither states the definition nor is implied by it.")]
theorem mapEquiv_isLocallyFinite (s : Slicing C) (hs : s.IsLocallyFinite C) :
    (s.mapEquiv Φ).IsLocallyFinite C := by
  obtain ⟨η, hη, hη2, hlf⟩ := hs.intervalFinite
  refine ⟨⟨η, hη, hη2, ?_⟩⟩
  intro t
  haveI : Fact (t - η < t + η) := ⟨by linarith⟩
  haveI : Fact ((t + η) - (t - η) ≤ 1) := ⟨by linarith⟩
  -- `show` past the statement's own `let a := t - η` bindings, which `intro`
  -- would otherwise consume before reaching the object.
  show ∀ E : Slicing.IntervalCat C (s.mapEquiv Φ) (t - η) (t + η),
    IsStrictArtinianObject E ∧ IsStrictNoetherianObject E
  intro E
  have hbig := hlf t ((autIntervalFunctor Φ s (t - η) (t + η)).obj E)
  letI := hbig.1
  letI := hbig.2
  refine ⟨?_, ?_⟩
  · exact isStrictArtinian_of_faithful_strict
      (autIntervalFunctor Φ s (t - η) (t + η))
      (fun f hf => autFunctor_strictMono Φ s (t - η) (t + η) f hf)
      (fun f _ hf => intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := s) (a := t - η) (b := t + η) f hf)
  · exact isStrictNoetherian_of_faithful_strict
      (autIntervalFunctor Φ s (t - η) (t + η))
      (fun f hf => autFunctor_strictMono Φ s (t - η) (t + η) f hf)
      (fun f _ hf => intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := s) (a := t - η) (b := t + η) f hf)

/-! ## The action -/

section ClassMap

-- `Λ` gets its own universe, as in `StabilityCondition/Symmetry/GLTilde/Action/Stability.lean`: nothing here
-- relates the class lattice to the category's universe, and tying them
-- together would make this track strictly less general than the `GL⁺` one.
variable {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ)

/-- **The `Aut` action on stability conditions.**

`Φ` moves the objects; `lam` carries it on the class lattice. The witness `m`
in `compat'` is *unchanged* — an autoequivalence moves an object without
moving its phase. -/
@[cites "stmt:a520a8d4f877:bridgeland2007.lem-8.2" (relation := one_way)
        (note := "The Aut half of Lemma 8.2, but this declaration is a map for a pair (Phi, lam), not the MulAction of bare Aut(D). Downstream HNMassUniqueness identifies the mass coordinate with Bridgeland's finite HN mass and AutFullIsometry proves exact preservation by AutPairQuot v; that quotient still carries extra compatible lattice data.")]
noncomputable def actStabAut (lam : Λ →+ Λ)
    (hlam : ∀ x : K₀ C, v (K₀.mapF Φ.inverse x) = lam (v x))
    (σ : StabilityCondition.WithClassMap C v) : StabilityCondition.WithClassMap C v where
  toWithClassMap :=
    { slicing := σ.slicing.mapEquiv Φ
      Z := σ.Z.comp lam
      compat' := by
        intro φ E hP hE
        have hE' : ¬ IsZero (Φ.inverse.obj E) := fun h =>
          hE (IsZero.of_iso (Φ.functor.map_isZero h) (Φ.counitIso.app E).symm)
        obtain ⟨m, hm, hZ⟩ := σ.compat' φ (Φ.inverse.obj E) hP hE'
        refine ⟨m, hm, ?_⟩
        show σ.Z (lam (v (K₀.of C E))) = _
        rw [← hlam, K₀.mapF_of]
        exact hZ }
  locallyFinite := mapEquiv_isLocallyFinite Φ σ.slicing σ.locallyFinite

@[simp] theorem actStabAut_slicing (lam : Λ →+ Λ) (hlam) (σ) :
    (actStabAut Φ v lam hlam σ).slicing = σ.slicing.mapEquiv Φ := rfl

@[simp] theorem actStabAut_Z (lam : Λ →+ Λ) (hlam) (σ) (x : Λ) :
    (actStabAut Φ v lam hlam σ).Z x = σ.Z (lam x) := rfl

end ClassMap

end CategoryTheory.Triangulated
