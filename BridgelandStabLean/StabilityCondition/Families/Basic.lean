/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Abstract interfaces for stability conditions in families

This file isolates the parts of Definition 20.5 and Definition 21.15 of
arXiv:1902.08184v4 which make sense without schemes, derived categories over a
base, or moduli stacks.  A caller supplies *all* geometric tests:

* `ChargeProbe` represents a base change together with a perfect object and
  the resulting pointwise charge (Definition 20.5(1));
* `OpenLocusProbe` represents one geometric-stability locus
  (Definition 20.5(2));
* `GenericSemistabilityProbe` represents the generic semistability test in
  the weak clause (2');
* `DedekindHNProblem` and `WeakDedekindHNProblem` name the witnesses demanded
  after every eligible essentially-finite-type Dedekind base change
  (clauses (3) and (3'));
* `BoundednessProblem` names the moduli problems whose boundedness is required
  by Definition 21.15(5).

The word `eligible` is deliberate: this library has no scheme or base-change
API, so it does not pretend to recognize Dedekind morphisms.  Instantiating
that predicate and the witness types is a geometric obligation of a client.
These interfaces turn those obligations into separately auditable
propositions; they do not prove any geometric theorem.
-/

namespace BridgelandStabLean.StabilityFamilies

universe u v u₁ u₂ u₃

/-- One universally quantified charge test.  Its point type and topology are
part of the supplied geometric datum. -/
structure ChargeProbe (A : Type v) where
  /-- Points of the chosen base change. -/
  Point : Type u
  /-- The topology on those points. -/
  topology : TopologicalSpace Point
  /-- The charge of the chosen object on every point. -/
  value : Point → A

/-- Definition 20.5(1) for one supplied base-change/object probe. -/
def ChargeProbe.IsLocallyConstant {A : Type v} (P : ChargeProbe A) : Prop :=
  @_root_.IsLocallyConstant P.Point A P.topology P.value

/-- Definition 20.5(1): every supplied base-change/object probe has locally
constant charge.  Universality is the outer quantifier over `J`. -/
def UniversallyLocallyConstantCharge {J : Type u} {A : Type v}
    (P : J → ChargeProbe A) : Prop :=
  ∀ j, (P j).IsLocallyConstant

/-- A constant charge probe on any topological space. -/
def ChargeProbe.constant (X : Type u) [TopologicalSpace X]
    {A : Type v} (a : A) : ChargeProbe A where
  Point := X
  topology := inferInstance
  value := Function.const X a

/-- Constant charge probes satisfy the local-constancy clause. -/
theorem ChargeProbe.constant_isLocallyConstant (X : Type u)
    [TopologicalSpace X] {A : Type v} (a : A) :
    (ChargeProbe.constant X a).IsLocallyConstant := by
  change _root_.IsLocallyConstant (Function.const X a)
  exact _root_.IsLocallyConstant.const a

/-- An indexed family of constant probes is universally locally constant. -/
theorem universallyLocallyConstantCharge_constant {J : Type u}
    (X : Type u) [TopologicalSpace X] {A : Type v} (a : J → A) :
    UniversallyLocallyConstantCharge
      (fun j ↦ ChargeProbe.constant X (a j)) :=
  fun j ↦ ChargeProbe.constant_isLocallyConstant X (a j)

/-- One supplied geometric-stability locus. -/
structure OpenLocusProbe where
  /-- Points of the chosen base change. -/
  Point : Type u
  /-- The topology on those points. -/
  topology : TopologicalSpace Point
  /-- The points where the supplied object is geometrically stable. -/
  locus : Set Point

/-- Definition 20.5(2) for one supplied geometric-stability probe. -/
def OpenLocusProbe.IsOpen (P : OpenLocusProbe) : Prop :=
  @_root_.IsOpen P.Point P.topology P.locus

/-- Definition 20.5(2): geometric stability is open for every supplied
base-change/object probe. -/
def UniversalOpenness {J : Type u} (P : J → OpenLocusProbe) : Prop :=
  ∀ j, (P j).IsOpen

/-- The full locus is a concrete openness probe. -/
def OpenLocusProbe.full (X : Type u) [TopologicalSpace X] : OpenLocusProbe where
  Point := X
  topology := inferInstance
  locus := Set.univ

/-- The full locus is open. -/
theorem OpenLocusProbe.full_isOpen (X : Type u) [TopologicalSpace X] :
    (OpenLocusProbe.full X).IsOpen := by
  change _root_.IsOpen (Set.univ : Set X)
  exact isOpen_univ

/-- A family of full loci satisfies universal openness. -/
theorem universalOpenness_full {J : Type u}
    (X : Type u) [TopologicalSpace X] :
    UniversalOpenness (fun _ : J ↦ OpenLocusProbe.full X) :=
  fun _ ↦ OpenLocusProbe.full_isOpen X

/-- One weak generic-semistability probe for Definition 20.5(2'). -/
structure GenericSemistabilityProbe where
  /-- Points of the chosen base change. -/
  Point : Type u
  /-- The topology on those points. -/
  topology : TopologicalSpace Point
  /-- The distinguished generic point. -/
  genericPoint : Point
  /-- The locus where the supplied object is semistable. -/
  semistableLocus : Set Point

/-- The weak generic-openness clause for one probe: semistability at the
generic point extends to an open neighbourhood of that point. -/
def GenericSemistabilityProbe.IsGenericallyOpen
    (P : GenericSemistabilityProbe) : Prop :=
  P.genericPoint ∈ P.semistableLocus →
    ∃ U : Set P.Point, @IsOpen P.Point P.topology U ∧
      P.genericPoint ∈ U ∧ U ⊆ P.semistableLocus

/-- Definition 20.5(2'): generic semistability is open for every supplied
probe. -/
def UniversalGenericOpenness {J : Type u}
    (P : J → GenericSemistabilityProbe) : Prop :=
  ∀ j, (P j).IsGenericallyOpen

/-- A probe whose entire space is semistable. -/
def GenericSemistabilityProbe.full (X : Type u) [TopologicalSpace X]
    (genericPoint : X) : GenericSemistabilityProbe where
  Point := X
  topology := inferInstance
  genericPoint := genericPoint
  semistableLocus := Set.univ

/-- The full semistable locus satisfies generic openness nonvacuously. -/
theorem GenericSemistabilityProbe.full_isGenericallyOpen
    (X : Type u) [TopologicalSpace X] (genericPoint : X) :
    (GenericSemistabilityProbe.full X genericPoint).IsGenericallyOpen := by
  intro _
  refine ⟨Set.univ, ?_, Set.mem_univ _, Set.Subset.rfl⟩
  exact @isOpen_univ X inferInstance

/-- A family of full semistable loci satisfies universal generic openness. -/
theorem universalGenericOpenness_full {J : Type u}
    (X : Type u) [TopologicalSpace X] (genericPoint : X) :
    UniversalGenericOpenness
      (fun _ : J ↦ GenericSemistabilityProbe.full X genericPoint) :=
  fun _ ↦ GenericSemistabilityProbe.full_isGenericallyOpen X genericPoint

/-- The abstract data of the ordinary HN integration problem after a proposed
Dedekind base change.  `IsEligible` is where a geometric client must encode
"essentially of finite type over a Dedekind scheme". -/
structure DedekindHNProblem (D : Type u) where
  /-- Which supplied base changes are in the source's quantified class. -/
  IsEligible : D → Prop
  /-- The type of relative HN structures to be constructed on a base change. -/
  HNStructure : D → Type v

/-- Definition 20.5(3): every eligible Dedekind base change carries a relative
HN structure. -/
def IntegratesAfterDedekindBaseChange {D : Type u}
    (P : DedekindHNProblem D) : Prop :=
  ∀ d, P.IsEligible d → Nonempty (P.HNStructure d)

/-- A constant HN problem with one supplied witness type. -/
def DedekindHNProblem.constant (D : Type u) (HN : Type v) :
    DedekindHNProblem D where
  IsEligible := fun _ ↦ True
  HNStructure := fun _ ↦ HN

/-- A nonempty witness type integrates the constant HN problem. -/
theorem integratesAfterDedekindBaseChange_constant
    (D : Type u) (HN : Type v) [Nonempty HN] :
    IntegratesAfterDedekindBaseChange (DedekindHNProblem.constant D HN) :=
  fun _ _ ↦ (inferInstance : Nonempty HN)

/-- The abstract weak HN integration problem of Definition 20.5(3').  The
extra predicate records that the induced zero-charge torsion subcategory is
noetherian after the same base change. -/
structure WeakDedekindHNProblem (D : Type u) where
  /-- Which supplied base changes are eligible. -/
  IsEligible : D → Prop
  /-- The type of induced weak HN structures. -/
  HNStructure : D → Type v
  /-- The noetherian zero-charge obligation on each base change. -/
  ZeroChargeNoetherian : D → Prop

/-- Definition 20.5(3'): every eligible base change has both a weak HN
structure and a noetherian zero-charge torsion subcategory. -/
def WeakIntegratesAfterDedekindBaseChange {D : Type u}
    (P : WeakDedekindHNProblem D) : Prop :=
  ∀ d, P.IsEligible d →
    Nonempty (P.HNStructure d) ∧ P.ZeroChargeNoetherian d

/-- A constant weak HN problem with a manifestly true noetherian predicate. -/
def WeakDedekindHNProblem.constant (D : Type u) (HN : Type v) :
    WeakDedekindHNProblem D where
  IsEligible := fun _ ↦ True
  HNStructure := fun _ ↦ HN
  ZeroChargeNoetherian := fun _ ↦ True

/-- A nonempty witness type integrates the constant weak HN problem. -/
theorem weakIntegratesAfterDedekindBaseChange_constant
    (D : Type u) (HN : Type v) [Nonempty HN] :
    WeakIntegratesAfterDedekindBaseChange
      (WeakDedekindHNProblem.constant D HN) :=
  fun _ _ ↦ ⟨(inferInstance : Nonempty HN), trivial⟩

/-- Abstract moduli problems and the caller-supplied predicate expressing
their boundedness. -/
structure BoundednessProblem (M : Type u) where
  /-- The geometric boundedness predicate for each numerical moduli problem. -/
  IsBounded : M → Prop

/-- Definition 21.15(5): every supplied semistable moduli problem is bounded. -/
def UniversalBoundedness {M : Type u} (P : BoundednessProblem M) : Prop :=
  ∀ m, P.IsBounded m

/-- The constant true boundedness problem.  This is a logical nonvacuity
witness, not a construction of a geometric bounded family. -/
def BoundednessProblem.trivial (M : Type u) : BoundednessProblem M where
  IsBounded := fun _ ↦ True

/-- The constant true boundedness problem satisfies the abstract interface. -/
theorem universalBoundedness_trivial (M : Type u) :
    UniversalBoundedness (BoundednessProblem.trivial M) :=
  fun _ ↦ trivial

/-- The three ordinary clauses of Definition 20.5, kept as separately named
fields so a review can inspect their quantifier boundaries independently. -/
structure OrdinaryDefinition20_5Conditions
    {JCharge : Type u₁} {JOpen : Type u₂} {D : Type u₃}
    (charge : JCharge → ChargeProbe ℂ)
    (stable : JOpen → OpenLocusProbe)
    (dedekind : DedekindHNProblem D) : Prop where
  /-- Definition 20.5(1). -/
  locallyConstantCharge : UniversallyLocallyConstantCharge charge
  /-- Definition 20.5(2). -/
  opennessOfGeometricStability : UniversalOpenness stable
  /-- Definition 20.5(3). -/
  dedekindHN : IntegratesAfterDedekindBaseChange dedekind

/-- The topological and relative-HN parts of the weak variant of Definition
20.5.  Clause (0), which refers to an actual weak stability function, is
bound to the repository's weak API in `Families.Weak`. -/
structure WeakDefinition20_5Conditions
    {JCharge : Type u₁} {JGeneric : Type u₂} {D : Type u₃}
    (charge : JCharge → ChargeProbe ℂ)
    (semistable : JGeneric → GenericSemistabilityProbe)
    (dedekind : WeakDedekindHNProblem D) : Prop where
  /-- Definition 20.5(1). -/
  locallyConstantCharge : UniversallyLocallyConstantCharge charge
  /-- Definition 20.5(2'). -/
  genericOpennessOfSemistability : UniversalGenericOpenness semistable
  /-- Definition 20.5(3'). -/
  dedekindWeakHN : WeakIntegratesAfterDedekindBaseChange dedekind

end BridgelandStabLean.StabilityFamilies
