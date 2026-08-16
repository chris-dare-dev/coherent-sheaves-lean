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
* **Nothing constructs a `DualKernel`.** That the quasi-inverse of a
  Fourier--Mukai equivalence is again one — with the derived-dual kernel
  `P^∨ ⊗ p^*ω[dim]` — is classical, and supplying it is geometry. What this
  file does is make the *consequences* of having one available: given a
  `DualKernel`, the class-lattice compatibility `actStab` needs is stated in
  terms of the dual kernel's own class map rather than the opaque
  `K₀.mapF Φ.inverse` (`actStabOfDual`), and the two kernels' class maps are
  proved mutually inverse (`transformK₀_dual_comp`).
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

section Dual

/-- A **dual kernel** for a kernel autoequivalence: a kernel presenting the
*quasi-inverse* as a transform of the same correspondence.

Classically this is the derived dual `P^∨ ⊗ p^*ω_X[dim X]`, and its existence is
a theorem about smooth projective varieties. Here it is supplied. What it buys
is that both directions of the equivalence become kernel-computable, which is
what turns `actStab`'s remaining hypothesis into kernel data. -/
structure DualKernel (A : KernelAutoequivalence C 𝒲) where
  /-- The kernel of the quasi-inverse. -/
  dual : 𝒲
  /-- The quasi-inverse is the transform with that kernel. -/
  invIso : A.equiv.inverse ≅ A.corr.transform dual

namespace DualKernel

variable {A} (D : DualKernel A)

variable [A.corr.pull.CommShift ℤ] [A.corr.push.CommShift ℤ]
  [A.corr.pull.IsTriangulated] [A.corr.push.IsTriangulated]
  [(A.corr.tensor.obj D.dual).CommShift ℤ]
  [(A.corr.tensor.obj D.dual).IsTriangulated]
  [A.equiv.inverse.CommShift ℤ] [A.equiv.inverse.IsTriangulated]

omit [IsTriangulated C] in
/-- **The quasi-inverse's action on classes is computed by the dual kernel.**
The mirror of `mapF_eq_transformK₀`, and the reason `actStabOfDual` can state
its hypothesis in kernel terms. -/
theorem mapF_inverse_eq_transformK₀ :
    K₀.mapF A.equiv.inverse = A.corr.transformK₀ D.dual := by
  have h : K₀.mapF A.equiv.inverse = K₀.map A.equiv.inverse := rfl
  rw [h]
  exact A.corr.K₀_map_eq_transformK₀ D.dual A.equiv.inverse D.invIso

variable [(A.corr.tensor.obj A.kernel).CommShift ℤ]
  [(A.corr.tensor.obj A.kernel).IsTriangulated]
  [A.equiv.functor.CommShift ℤ] [A.equiv.functor.IsTriangulated]

omit [IsTriangulated C] in
/-- **The two kernels' class maps are mutually inverse.**

Proved from `K₀.map_comp_map_eq_id` on the equivalence's unit, then transported
across both kernel identifications. Neither convolution nor an identity kernel
is involved: the inverse relation comes from the supplied equivalence, not from
`conv P P^∨ ≅ 𝒪_Δ`. -/
theorem transformK₀_dual_comp :
    (A.corr.transformK₀ D.dual).comp (A.corr.transformK₀ A.kernel) =
      AddMonoidHom.id (K₀ C) := by
  rw [← A.mapF_eq_transformK₀, ← D.mapF_inverse_eq_transformK₀]
  exact K₀.map_comp_map_eq_id A.equiv.functor A.equiv.inverse
    A.equiv.unitIso.symm

omit [IsTriangulated C] in
/-- The composite in the other order is also the identity. -/
theorem transformK₀_comp_dual :
    (A.corr.transformK₀ A.kernel).comp (A.corr.transformK₀ D.dual) =
      AddMonoidHom.id (K₀ C) := by
  rw [← A.mapF_eq_transformK₀, ← D.mapF_inverse_eq_transformK₀]
  exact K₀.map_comp_map_eq_id A.equiv.inverse A.equiv.functor
    A.equiv.counitIso

end DualKernel

end Dual

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

section OfDual

variable (D : DualKernel A)
  [A.corr.pull.CommShift ℤ] [A.corr.push.CommShift ℤ]
  [A.corr.pull.IsTriangulated] [A.corr.push.IsTriangulated]
  [(A.corr.tensor.obj D.dual).CommShift ℤ]
  [(A.corr.tensor.obj D.dual).IsTriangulated]

/-- **Transport with the compatibility stated in kernel terms.**

Identical to `actStab` except for its hypothesis: `hlam` is asked against
`transformK₀ D.dual`, which is computed from the dual kernel, rather than
against `K₀.mapF A.equiv.inverse`, which is opaque. `mapF_inverse_eq_transformK₀`
identifies the two, so this is the same transport with a checkable premise. -/
def actStabOfDual (lam : Λ →+ Λ)
    (hlam : ∀ x : K₀ C, v (A.corr.transformK₀ D.dual x) = lam (v x))
    (σ : StabilityCondition.WithClassMap C v) :
    StabilityCondition.WithClassMap C v :=
  A.actStab v lam (fun x => by
    rw [show K₀.mapF A.equiv.inverse = A.corr.transformK₀ D.dual from
      D.mapF_inverse_eq_transformK₀]
    exact hlam x) σ

@[simp]
theorem actStabOfDual_slicing (lam : Λ →+ Λ) (hlam) (σ) :
    (A.actStabOfDual v D lam hlam σ).slicing =
      CategoryTheory.Triangulated.Slicing.mapEquiv σ.slicing A.equiv :=
  rfl

@[simp]
theorem actStabOfDual_Z (lam : Λ →+ Λ) (hlam) (σ) (x : Λ) :
    (A.actStabOfDual v D lam hlam σ).Z x = σ.Z (lam x) :=
  rfl

end OfDual

end Action

end KernelAutoequivalence

end

end CategoryTheory.Triangulated.StabilityCondition.Symmetry
