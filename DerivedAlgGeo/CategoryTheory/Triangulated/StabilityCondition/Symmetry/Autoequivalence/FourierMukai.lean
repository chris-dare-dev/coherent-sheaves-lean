/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.GrothendieckGroup
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Stability.Transport

/-!
# Kernel functors acting on stability conditions

`Symmetry/Autoequivalence/Stability/Transport` transports a stability condition
along an autoequivalence. `Triangulated.FourierMukai` builds kernel functors.
This file joins them: a kernel functor that happens to be an autoequivalence
acts on `StabilityCondition.WithClassMap`, and its action on classes is
computed by its kernel.

That second half is the point. `actStabAut` already takes any autoequivalence;
what a `KernelAutoequivalence` adds is that the induced map on `K₀` is
`transformK₀ K` — so the action on the central charge is determined by the
kernel rather than by the functor's construction.

## Direction of dependence

This file lives in the stability track and imports the generic
Fourier--Mukai modules, never the reverse. `mapF` and `actStabAut` are both
stability-track declarations, so a file under
`CategoryTheory/Triangulated/FourierMukai/` could not state any of this
without pointing a generic module at a specialized one — the layering that
issue #453 removed.

## What this file does not assert

* **Nothing constructs a `KernelAutoequivalence`.** The equivalence and the
  isomorphism to a transform are both supplied. That a Fourier--Mukai transform
  with a suitable kernel *is* an equivalence is the classical theorem, and it
  needs the geometry the abstract `Correspondence` does not carry.
* Nothing says the quasi-inverse is again a kernel functor. Classically it is,
  with the derived-dual kernel; here the inverse is just a functor, which is why
  `actStab` takes the class-lattice compatibility as a hypothesis rather than
  deriving it from a second kernel.
* No orbit, group action, or `MulAction` structure. `actStab` is a single
  transport, matching `actStabAut`, and composing two of them is not shown to
  be the transport of a convolved kernel.
* Nothing about Bridgeland's `Stab(X)` as a manifold, and no continuity or
  local-homeomorphism claim for the induced map.
-/

universe w u u' t

namespace CategoryTheory.Triangulated.StabilityCondition.Symmetry

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated CategoryTheory.Triangulated.FourierMukai

noncomputable section

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
  {𝒲 : Type t} [Category.{w} 𝒲] [HasZeroObject 𝒲] [HasShift 𝒲 ℤ]
  [Preadditive 𝒲] [∀ n : ℤ, (shiftFunctor 𝒲 n).Additive] [Pretriangulated 𝒲]

/-- A **kernel autoequivalence**: an autoequivalence of `C` presented as a
Fourier--Mukai transform.

The correspondence, the kernel, the equivalence, and the isomorphism between
them are all supplied. Nothing here proves that any transform is an
equivalence — that is the classical theorem and it needs geometry. -/
structure KernelAutoequivalence (C : Type u) [Category.{w} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (𝒲 : Type t) [Category.{w} 𝒲] [HasZeroObject 𝒲]
    [HasShift 𝒲 ℤ] [Preadditive 𝒲] [∀ n : ℤ, (shiftFunctor 𝒲 n).Additive]
    [Pretriangulated 𝒲] where
  /-- The correspondence from `C` to itself. -/
  corr : Correspondence C C 𝒲
  /-- The kernel. -/
  kernel : 𝒲
  /-- The autoequivalence. -/
  equiv : C ≌ C
  /-- Its functor is the transform with that kernel. -/
  iso : equiv.functor ≅ corr.transform kernel

namespace KernelAutoequivalence

variable (A : KernelAutoequivalence C 𝒲)

omit [IsTriangulated C] in
/-- On classes of objects, the autoequivalence and its transform agree.

Stated this way round rather than as a `simp` lemma about `K₀.mapF`: the
existing `K₀.mapF_of` already rewrites that left-hand side, so a lemma phrased
against it would not be in simp-normal form. -/
theorem of_obj_eq (E : C) :
    K₀.of C (A.equiv.functor.obj E) =
      K₀.of C ((A.corr.transform A.kernel).obj E) :=
  K₀.of_iso C (A.iso.app E)

section ClassMap

variable [A.corr.pull.CommShift ℤ] [(A.corr.tensor.obj A.kernel).CommShift ℤ]
  [A.corr.push.CommShift ℤ] [A.corr.pull.IsTriangulated]
  [(A.corr.tensor.obj A.kernel).IsTriangulated] [A.corr.push.IsTriangulated]
  [A.equiv.functor.CommShift ℤ] [A.equiv.functor.IsTriangulated]

omit [IsTriangulated C] in
/-- **The action on classes is computed by the kernel.**

`K₀.mapF` and `K₀.map` agree on an endofunctor — both are
`K₀.lift C (fun X ↦ K₀.of C (F.obj X))` — so this is
`Correspondence.K₀_map_eq_transformK₀` transported across that identification
and the supplied isomorphism. It is what makes the kernel, rather than the
functor's construction, the thing that determines the transported charge. -/
theorem mapF_eq_transformK₀ :
    K₀.mapF A.equiv.functor = A.corr.transformK₀ A.kernel := by
  have h : K₀.mapF A.equiv.functor = K₀.map A.equiv.functor := rfl
  rw [h]
  exact A.corr.K₀_map_eq_transformK₀ A.kernel A.equiv.functor A.iso

end ClassMap

section Action

variable {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ)
  [A.equiv.functor.Additive] [A.equiv.inverse.Additive]
  [A.equiv.functor.CommShift ℤ] [A.equiv.inverse.CommShift ℤ]
  [A.equiv.functor.IsTriangulated] [A.equiv.inverse.IsTriangulated]

/-- **A kernel autoequivalence transports a stability condition.**

A thin specialisation of `actStabAut`, and deliberately so: the content is that
the Fourier--Mukai side can supply the autoequivalence at all, not that the
transport needs redoing.

`hlam` is stated for the *quasi-inverse*, following `actStabAut`. Classically
the quasi-inverse of a Fourier--Mukai equivalence is again one, with the
derived-dual kernel, and `hlam` would follow from `mapF_eq_transformK₀` for
that kernel; nothing here supplies it. -/
def actStab (lam : Λ →+ Λ)
    (hlam : ∀ x : K₀ C, v (K₀.mapF A.equiv.inverse x) = lam (v x))
    (σ : StabilityCondition.WithClassMap C v) :
    StabilityCondition.WithClassMap C v :=
  actStabAut A.equiv v lam hlam σ

@[simp]
theorem actStab_slicing (lam : Λ →+ Λ) (hlam) (σ) :
    (A.actStab v lam hlam σ).slicing =
      CategoryTheory.Triangulated.Slicing.mapEquiv σ.slicing A.equiv :=
  rfl

@[simp]
theorem actStab_Z (lam : Λ →+ Λ) (hlam) (σ) (x : Λ) :
    (A.actStab v lam hlam σ).Z x = σ.Z (lam x) :=
  rfl

end Action

end KernelAutoequivalence

end

end CategoryTheory.Triangulated.StabilityCondition.Symmetry
