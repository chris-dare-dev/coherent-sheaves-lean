/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Module.GradedModule
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Localization.Module

/-!
# Degree-zero homogeneous localization of graded modules

This file supplies the algebraic input missing from Mathlib's `Proj` API. Mathlib already
constructs the degree-zero homogeneous localization ring `HomogeneousLocalization 𝒜 S` and
the ordinary localized module `LocalizedModule S M`. We isolate inside the latter the fractions
whose module numerator and ring denominator lie in matching graded pieces.

The construction is intentionally indexed by the same additive grading monoid on the ring and
the module. Integer shifts, which require reconciling the natural grading used by `Proj` with an
integer grading on modules, belong to the later twisting-sheaf layer.
-/

noncomputable section

open DirectSum SetLike

namespace CohLean.AlgebraicGeometry.Proj

universe u v

variable {ι A M σA σM : Type*}
variable [AddCommMonoid ι] [DecidableEq ι]
variable [CommRing A] [AddCommGroup M] [Module A M]
variable [SetLike σA A] [AddSubgroupClass σA A]
variable [SetLike σM M] [AddSubgroupClass σM M]
variable (𝒜 : ι → σA) (𝓜 : ι → σM)
variable [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜]
variable (S : Submonoid A)

/-! ## Homogeneous fractions -/

/-- A module fraction whose numerator and denominator lie in matching graded pieces. -/
structure NumDenSameDeg where
  deg : ι
  num : 𝓜 deg
  den : 𝒜 deg
  den_mem : (den : A) ∈ S

namespace NumDenSameDeg

variable {𝒜 𝓜 S}

/-- Forget the grading certificate and view a homogeneous module fraction in the ordinary
localized module. -/
def embedding (c : NumDenSameDeg 𝒜 𝓜 S) : LocalizedModule S M :=
  LocalizedModule.mk (S := S) (c.num : M) (⟨(c.den : A), c.den_mem⟩ : S)

omit [AddCommMonoid ι] [DecidableEq ι] [AddSubgroupClass σA A]
    [AddSubgroupClass σM M] [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜] in
@[simp]
theorem embedding_eq (c : NumDenSameDeg 𝒜 𝓜 S) :
    c.embedding = LocalizedModule.mk (S := S) (c.num : M)
      (⟨(c.den : A), c.den_mem⟩ : S) :=
  rfl

end NumDenSameDeg

/-! ## The degree-zero submodule -/

/-- Restrict scalars on the ordinary localized module along the inclusion of the degree-zero
homogeneous localization into the full localization. -/
noncomputable instance localizedModuleModule :
    Module (HomogeneousLocalization 𝒜 S) (LocalizedModule S M) :=
  Module.compHom _ (algebraMap (HomogeneousLocalization 𝒜 S) (Localization S))

/-- An ordinary localized-module element is degree zero if it has a representative whose module
numerator and ring denominator lie in matching graded pieces. -/
def IsDegreeZero (z : LocalizedModule S M) : Prop :=
  ∃ c : NumDenSameDeg 𝒜 𝓜 S, c.embedding = z

omit [SetLike.GradedSMul 𝒜 𝓜] in
theorem isDegreeZero_zero : IsDegreeZero 𝒜 𝓜 S (0 : LocalizedModule S M) := by
  refine ⟨⟨0, ⟨0, zero_mem _⟩, ⟨1, one_mem_graded _⟩, one_mem S⟩, ?_⟩
  simp [NumDenSameDeg.embedding]

theorem IsDegreeZero.add {x y : LocalizedModule S M}
    (hx : IsDegreeZero 𝒜 𝓜 S x) (hy : IsDegreeZero 𝒜 𝓜 S y) :
    IsDegreeZero 𝒜 𝓜 S (x + y) := by
  obtain ⟨p, rfl⟩ := hx
  obtain ⟨q, rfl⟩ := hy
  refine ⟨
    { deg := p.deg + q.deg
      num := ⟨(q.den : A) • (p.num : M) + (p.den : A) • (q.num : M), ?_⟩
      den := ⟨(p.den : A) * (q.den : A), SetLike.mul_mem_graded p.den.2 q.den.2⟩
      den_mem := S.mul_mem p.den_mem q.den_mem }, ?_⟩
  · exact add_mem
      (add_comm q.deg p.deg ▸ SetLike.GradedSMul.smul_mem q.den.2 p.num.2)
      (SetLike.GradedSMul.smul_mem p.den.2 q.num.2)
  · simp only [NumDenSameDeg.embedding]
    rw [LocalizedModule.mk_add_mk]
    rw [LocalizedModule.mk_eq]
    exact ⟨1, by simp⟩

omit [AddCommMonoid ι] [DecidableEq ι] [AddSubgroupClass σA A]
    [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜] in
theorem IsDegreeZero.neg {x : LocalizedModule S M} (hx : IsDegreeZero 𝒜 𝓜 S x) :
    IsDegreeZero 𝒜 𝓜 S (-x) := by
  obtain ⟨p, rfl⟩ := hx
  refine ⟨
    { deg := p.deg
      num := ⟨-(p.num : M), neg_mem p.num.2⟩
      den := p.den
      den_mem := p.den_mem }, ?_⟩
  simpa only [NumDenSameDeg.embedding] using
    (LocalizedModule.mk_neg
      (S := S) (M := M) (m := (p.num : M))
      (s := (⟨(p.den : A), p.den_mem⟩ : S)))

omit [AddSubgroupClass σM M] in
theorem IsDegreeZero.smul (a : HomogeneousLocalization 𝒜 S) {x : LocalizedModule S M}
    (hx : IsDegreeZero 𝒜 𝓜 S x) : IsDegreeZero 𝒜 𝓜 S (a • x) := by
  obtain ⟨p, rfl⟩ := hx
  refine ⟨
    { deg := a.deg + p.deg
      num := ⟨a.num • (p.num : M), SetLike.GradedSMul.smul_mem a.num_mem_deg p.num.2⟩
      den := ⟨a.den * (p.den : A), SetLike.mul_mem_graded a.den_mem_deg p.den.2⟩
      den_mem := S.mul_mem a.den_mem p.den_mem }, ?_⟩
  change LocalizedModule.mk (S := S) (a.num • (p.num : M))
    (⟨a.den * (p.den : A), S.mul_mem a.den_mem p.den_mem⟩ : S) =
      (algebraMap (HomogeneousLocalization 𝒜 S) (Localization S) a) •
        LocalizedModule.mk (S := S) (p.num : M) (⟨(p.den : A), p.den_mem⟩ : S)
  rw [HomogeneousLocalization.algebraMap_apply]
  rw [a.eq_num_div_den]
  rw [LocalizedModule.mk_smul_mk]
  rw [LocalizedModule.mk_eq]
  exact ⟨1, by simp⟩

/-- The degree-zero homogeneous localization as a submodule of the ordinary localized module. -/
def degreeZeroSubmodule :
    Submodule (HomogeneousLocalization 𝒜 S) (LocalizedModule S M) where
  carrier := IsDegreeZero 𝒜 𝓜 S
  zero_mem' := isDegreeZero_zero 𝒜 𝓜 S
  add_mem' := fun hx hy ↦
    IsDegreeZero.add (𝒜 := 𝒜) (𝓜 := 𝓜) (S := S) hx hy
  smul_mem' := fun a _ hx ↦
    IsDegreeZero.smul (𝒜 := 𝒜) (𝓜 := 𝓜) (S := S) a hx

/-- The degree-zero homogeneous localization of the graded module `M`. -/
abbrev DegreeZeroLocalization := degreeZeroSubmodule (𝓜 := 𝓜) 𝒜 S

namespace DegreeZeroLocalization

variable {𝒜 𝓜 S}

/-- Construct a degree-zero localized element from a certified homogeneous fraction. -/
def mk (c : NumDenSameDeg 𝒜 𝓜 S) : DegreeZeroLocalization 𝒜 𝓜 S :=
  ⟨c.embedding, ⟨c, rfl⟩⟩

@[simp]
theorem coe_mk (c : NumDenSameDeg 𝒜 𝓜 S) :
    ((mk c : DegreeZeroLocalization 𝒜 𝓜 S) : LocalizedModule S M) = c.embedding :=
  rfl

/-- Every degree-zero localized element has a homogeneous numerator and denominator. -/
theorem mk_surjective :
    Function.Surjective (mk : NumDenSameDeg 𝒜 𝓜 S → DegreeZeroLocalization 𝒜 𝓜 S) := by
  rintro ⟨z, ⟨c, hc⟩⟩
  exact ⟨c, Subtype.ext hc⟩

@[ext]
theorem ext {x y : DegreeZeroLocalization 𝒜 𝓜 S}
    (h : (x : LocalizedModule S M) = y) : x = y :=
  Subtype.ext h

/-- Equality of homogeneous fractions is the ordinary localized-module equality criterion. -/
theorem mk_eq_mk_iff (p q : NumDenSameDeg 𝒜 𝓜 S) :
    mk p = mk q ↔
      ∃ u : S,
        (u : A) • (q.den : A) • (p.num : M) =
          (u : A) • (p.den : A) • (q.num : M) := by
  constructor
  · intro h
    have h' : p.embedding = q.embedding := congr_arg Subtype.val h
    simp only [NumDenSameDeg.embedding] at h'
    rw [LocalizedModule.mk_eq] at h'
    simpa only [Submonoid.smul_def, Submonoid.coe_mul] using h'
  · intro h
    apply ext
    simp only [coe_mk, NumDenSameDeg.embedding]
    rw [LocalizedModule.mk_eq]
    simpa only [Submonoid.smul_def, Submonoid.coe_mul] using h

@[simp]
theorem coe_zero :
    ((0 : DegreeZeroLocalization 𝒜 𝓜 S) : LocalizedModule S M) = 0 :=
  rfl

@[simp]
theorem coe_add (x y : DegreeZeroLocalization 𝒜 𝓜 S) :
    ((x + y : DegreeZeroLocalization 𝒜 𝓜 S) : LocalizedModule S M) = x + y :=
  rfl

@[simp]
theorem coe_neg (x : DegreeZeroLocalization 𝒜 𝓜 S) :
    ((-x : DegreeZeroLocalization 𝒜 𝓜 S) : LocalizedModule S M) = -x :=
  rfl

@[simp]
theorem coe_smul (a : HomogeneousLocalization 𝒜 S)
    (x : DegreeZeroLocalization 𝒜 𝓜 S) :
    ((a • x : DegreeZeroLocalization 𝒜 𝓜 S) : LocalizedModule S M) = a • (x : LocalizedModule S M) :=
  rfl

/-! ### Localization away from one homogeneous element -/

/-- The degree-zero fraction `m / fⁿ` when `f` has degree `d` and `m` has degree `n • d`. -/
def awayMk {f : A} {d : ι} (hf : f ∈ 𝒜 d) (n : ℕ) (m : M)
    (hm : m ∈ 𝓜 (n • d)) : DegreeZeroLocalization 𝒜 𝓜 (.powers f) :=
  mk
    { deg := n • d
      num := ⟨m, hm⟩
      den := ⟨f ^ n, SetLike.pow_mem_graded n hf⟩
      den_mem := ⟨n, rfl⟩ }

@[simp]
theorem coe_awayMk {f : A} {d : ι} (hf : f ∈ 𝒜 d) (n : ℕ) (m : M)
    (hm : m ∈ 𝓜 (n • d)) :
    ((awayMk hf n m hm : DegreeZeroLocalization 𝒜 𝓜 (.powers f)) :
      LocalizedModule (.powers f) M) =
        LocalizedModule.mk m (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f) :=
  rfl

end DegreeZeroLocalization

/-! ## Functoriality -/

/-- An `A`-linear map which preserves every graded piece. Mathlib has a bundled graded ring map,
but currently no corresponding bundled map for internally graded modules. -/
@[ext]
structure GradedLinearMap {N σN : Type*} [AddCommGroup N] [Module A N]
    [SetLike σN N] [AddSubgroupClass σN N] (𝓝 : ι → σN) where
  toLinearMap : M →ₗ[A] N
  map_mem : ∀ i (m : M), m ∈ 𝓜 i → toLinearMap m ∈ 𝓝 i

namespace GradedLinearMap

variable {N σN : Type*} [AddCommGroup N] [Module A N]
variable [SetLike σN N] [AddSubgroupClass σN N]
variable (𝓝 : ι → σN) [SetLike.GradedSMul 𝒜 𝓝]

/-- The ordinary localized map underlying a grading-preserving linear map. -/
noncomputable def localized (f : GradedLinearMap (A := A) 𝓜 𝓝) :
    LocalizedModule S M →ₗ[Localization S] LocalizedModule S N :=
  LocalizedModule.map S f.toLinearMap

omit [AddCommMonoid ι] [DecidableEq ι] [AddSubgroupClass σM M] in
@[simp]
theorem localized_mk (f : GradedLinearMap (A := A) 𝓜 𝓝) (m : M) (s : S) :
    localized (𝓜 := 𝓜) (𝓝 := 𝓝) (S := S) f (LocalizedModule.mk m s) =
      LocalizedModule.mk (f.toLinearMap m) s := by
  exact LocalizedModule.map_mk S f.toLinearMap m s

/-- A grading-preserving linear map sends degree-zero homogeneous localizations to degree-zero
homogeneous localizations. -/
noncomputable def map (f : GradedLinearMap (A := A) 𝓜 𝓝) :
    DegreeZeroLocalization 𝒜 𝓜 S →ₗ[HomogeneousLocalization 𝒜 S]
      DegreeZeroLocalization 𝒜 𝓝 S where
  toFun z := by
    refine ⟨localized (𝓜 := 𝓜) (𝓝 := 𝓝) (S := S) f z, ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg
        num := ⟨f.toLinearMap c.num, f.map_mem c.deg c.num c.num.2⟩
        den := c.den
        den_mem := c.den_mem }, ?_⟩
    rw [← hc]
    simp only [NumDenSameDeg.embedding]
    rw [localized_mk (𝓜 := 𝓜) (𝓝 := 𝓝) (S := S)]
  map_add' x y := by
    apply DegreeZeroLocalization.ext
    exact (localized (𝓜 := 𝓜) (𝓝 := 𝓝) (S := S) f).map_add x y
  map_smul' a x := by
    apply DegreeZeroLocalization.ext
    exact (localized (𝓜 := 𝓜) (𝓝 := 𝓝) (S := S) f).map_smul (algebraMap _ _ a) x

@[simp]
theorem map_mk (f : GradedLinearMap (A := A) 𝓜 𝓝) (c : NumDenSameDeg 𝒜 𝓜 S) :
    map (𝒜 := 𝒜) (𝓜 := 𝓜) (𝓝 := 𝓝) (S := S) f (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg
          num := ⟨f.toLinearMap c.num, f.map_mem c.deg c.num c.num.2⟩
          den := c.den
          den_mem := c.den_mem } := by
  apply DegreeZeroLocalization.ext
  exact localized_mk (𝓜 := 𝓜) (𝓝 := 𝓝) (S := S) f c.num ⟨c.den, c.den_mem⟩

end GradedLinearMap

end CohLean.AlgebraicGeometry.Proj
