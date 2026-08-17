/-
GeometricLedgers slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearYoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearCoyoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm
import DerivedAlgGeo.LinearAlgebra
open CategoryTheory.Triangulated

/-! ## The geometric Fourier--Mukai correspondence: a dependency ledger

INHABITANT-FREE BY DESIGN. Nothing constructs a `HasDerivedPushforward` or a
`HasDerivedTensor`, and no scheme is shown to admit either, so a clean axiom
list here is emphatically NOT evidence that a geometric Fourier--Mukai
transform exists in this repository. What it says is that
`geometricCorrespondence` assembles a `Correspondence` from exactly three
inputs -- the existing derived-pullback contract, a supplied derived tensor,
and a supplied derived pushforward -- and from nothing else.

Derived pushforward and derived tensor on `D^b(Coh)` do not exist anywhere in
the repository; this file names them rather than building them. The middle
scheme is deliberately NOT required to be a product: `Correspondence` does not
consume that, and it is the composition law (`ConvolutionData`) that needs it.
-/

#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedPushforward
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedPushforward.derivedPushforward
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedPushforward.additive
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedPushforward.commShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedPushforward.isTriangulated
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.derivedPushforward
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedTensor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedTensor.derivedTensor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedTensor.additive
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedTensor.commShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedTensor.isTriangulated
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.derivedTensor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricCorrespondence
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricCorrespondence_pull
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricCorrespondence_tensor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricCorrespondence_push
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.derivedPushforward_additive
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.derivedPushforwardCommShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.derivedPushforward_isTriangulated
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.derivedTensor_additive
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.derivedTensorCommShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.derivedTensor_isTriangulated

/-! ## Convolution of kernels: the second ledger

INHABITANT-FREE, like the first. Nothing constructs an instance of any of the
seven input classes.

What this ledger buys is that BOTH fields of `ConvolutionData` stop being
supplied: `convKernel` is the classical
`R(pi_XW)_*(pi_XY^* P (x)^L pi_YW^* Q)` built from functors the first ledger
already names, and `geometricCompIso` DERIVES Prop. 5.10 from seven named
inputs -- projection formula (both slots), flat base change, monoidality of
pullback, tensor associativity, and the two route-agreement classes. The old
`HasConvolutionComparison`, which supplied compIso whole, is deleted.

A clean axiom line on `geometricCompIso` means the derivation adds nothing
beyond its inputs; it is NOT evidence that any input is constructible, and
nothing here constructs a `Correspondence`. -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TripleProductGeometry
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TripleProductGeometry.mk.inj
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TripleProductGeometry.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TripleProductGeometry.triple
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TripleProductGeometry.πXY
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TripleProductGeometry.πYW
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TripleProductGeometry.πXW
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.convKernel
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasProjectionFormula
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasProjectionFormula.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasFlatBaseChange
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasFlatBaseChange.comm
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasFlatBaseChange.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedPullbackTensor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedPullbackTensor.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedTensorAssoc
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasDerivedTensorAssoc.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasProjectionFormulaRight
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasProjectionFormulaRight.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasCommonPullbackRoute
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasCommonPullbackRoute.comm
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasCommonPullbackRoute.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasCommonPushforwardRoute
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasCommonPushforwardRoute.comm
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasCommonPushforwardRoute.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricCompIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricConvolutionData

/-! ## The unit kernel: the third ledger

INHABITANT-FREE, like the first two. `diagonalKernel` is a DEFINITION
(`Rdelta_*` of the tensor unit) and `geometricUnitIso` DERIVES that its
transform is the identity from four inputs: `HasProjectionFormulaRight` at
the diagonal (an existing class, consumed at a second site), `HasTensorUnit`,
and the two retraction classes, whose `comm` triangle identities are guards
the derivation deliberately does not consume. `DualKernel` remains a named
absence: its classical formula needs derived duals and a dualizing complex,
which have no substrate here. A clean axiom line on `geometricUnitIso` means
the derivation adds nothing beyond its inputs, not that any input is
constructible.
-/

#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasTensorUnit
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasTensorUnit.unit
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasTensorUnit.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPullbackRetraction
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPullbackRetraction.comm
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPullbackRetraction.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPushforwardRetraction
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPushforwardRetraction.comm
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPushforwardRetraction.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.diagonalKernel
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricUnitIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricUnitKernelData

/-! ## Associativity of the geometric convolution: the quadruple product

INHABITANT-FREE. `geometricConvolutionAssoc` DERIVES the kernel-level
`(P * Q) * R iso P * (Q * R)` for `convKernel` through a supplied quadruple
product, consuming the existing comparison classes at new instance sites --
including `HasDerivedTensorAssoc`, the consumption site #542 promised -- plus
two new factorization classes whose `comm` triangle identities are unconsumed
guards. `geometricConvolutionAssocData` then has zero supplied fields. A
clean axiom line means the derivation adds nothing beyond its inputs; nothing
constructs any input, and nothing states a pentagon. -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPullbackFactorization
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPullbackFactorization.comm
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPullbackFactorization.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPushforwardFactorization
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPushforwardFactorization.comm
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasPushforwardFactorization.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.mk.inj
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.quad
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.ρ₁₂
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.ρ₂₃
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.ρ₃₄
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.ρ₁₄
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.σ₁₂₃
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.σ₂₃₄
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.σ₁₃₄
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.QuadrupleProductGeometry.σ₁₂₄
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.quadKernel
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.leftAssocIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.rightAssocIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricConvolutionAssoc
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricConvolutionAssocData

/-! ## The unit laws for the geometric convolution

INHABITANT-FREE. Both kernel-level unit laws are DERIVED for `convKernel`
with unit kernel `diagonalKernel`, each through a supplied section `tau` of
the relevant triple product: the left law consumes `HasProjectionFormula` at
`tau`, the right law `HasProjectionFormulaRight` at `tau` -- the standing
slot separation -- plus the retraction classes of the third ledger at their
second consumption site and one new pulled-unit unitor class per slot.
Nothing constructs any input; no triangle identity relates the unit and
associativity layers. -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasUnitPullbackRightUnitor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasUnitPullbackRightUnitor.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasUnitPullbackLeftUnitor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasUnitPullbackLeftUnitor.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricConvUnitLeft
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricConvUnitRight
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricConvolutionLeftUnitData
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.geometricConvolutionRightUnitData
