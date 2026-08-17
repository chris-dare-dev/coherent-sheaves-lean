/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families.KernelCorrespondence
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Convolution

/-!
# Convolution of Fourier--Mukai kernels: the second ledger

`KernelCorrespondence.lean` reduced a geometric `Correspondence` to three named
inputs. This file does the same for the **composition law**: the abstract
`ConvolutionData` asks for a kernel operation `conv` *and* the family of
isomorphisms `Φ_P ⋙ Φ_Q ≅ Φ_{conv P Q}`, both as supplied data, and this ledger
reduces that.

## What this ledger buys: `conv` stops being supplied

Classically `conv P Q = Rπ_{XW*}(π_{XY}^* P ⊗^L π_{YW}^* Q)` on the triple
product. Every functor in that expression is one the *first* ledger already
names — two derived pullbacks, one derived tensor, one derived pushforward —
so given a triple product with its three projections, `convKernel` is a
**definition**. `ConvolutionData`'s first field stops being an obligation.

Its second field does not. `compIso` is Prop. 5.10 and is a genuine theorem;
proving it needs the projection formula and flat base change, which are named
here as `HasProjectionFormula` and `HasFlatBaseChange` but **not** used to
derive anything. The honest statement of this ledger's effect is therefore:

> `ConvolutionData` went from two supplied fields to one, and the remaining
> one now has its two classical inputs named next to it.

## Where the product finally becomes load-bearing

`KernelCorrespondence.lean` deliberately did *not* require its middle scheme to
be a product, because `Correspondence` does not consume that. Here the
situation is different and the docstrings say so: `compIso` is *false* without
it. The base-change square that the classical proof uses is the one formed by
two projections of an actual fibre product, and there is no substitute.

`TripleProductGeometry` therefore carries the projections as data but still
does not *assert* that the objects are products — because nothing in this file
consumes that assertion either. What consumes it is a proof of `compIso`, which
this file does not contain. A caller discharging `HasConvolutionComparison`
is the one who will need the product structure, and the class docstring says so.
Asserting it here would be an unconsumed hypothesis, which is the thing both
review rounds attacked.

## What this file does not assert

* **Nothing constructs a `HasProjectionFormula`, a `HasFlatBaseChange`, or a
  `HasConvolutionComparison`**, and no scheme is shown to admit any of them.
  Inhabitant-free, exactly like the first ledger.
* **The projection formula and flat base change are named but not consumed.**
  They are stated because they are what a proof of `compIso` would use, and
  naming them is the point of a ledger — but this file derives nothing from
  them, and a reader must not take their presence as progress toward `compIso`.
  Deriving `compIso` from them is the next piece of work, not this one.
* No associativity of convolution — `Convolution.lean` says that needs a second
  data layer relating the two bracketings, and this ledger does not supply it.
* No unit: `𝒪_Δ` along the diagonal is absent, so `UnitKernelData` is still
  unreachable geometrically.
-/

universe u

namespace CategoryTheory.Triangulated.StabilityCondition.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated CategoryTheory.Triangulated.FourierMukai
open AlgebraicGeometry
open SchemeBaseChange

variable {S : Scheme.{u}}

section TripleProduct

/-- **The triple product and its three projections, supplied.**

`triple` plays `X ×_S Y ×_S W`, and the three morphisms play the projections
onto the pairwise products `Z₁ = X ×_S Y`, `Z₂ = Y ×_S W`, `Z₃ = X ×_S W`.

Carried as data rather than constructed. `Over S` does have binary products
when `Scheme` has pullbacks, and it does, but nothing makes the resulting
objects locally Noetherian — which `Dᵇ(Coh)` requires — so a caller supplies
the objects together with that hypothesis anyway.

**Not asserted: that any of these objects is a product.** Nothing in this file
consumes it. What consumes it is a proof of `HasConvolutionComparison`, which
this file does not contain; see that class's docstring. -/
structure TripleProductGeometry (Z₁ Z₂ Z₃ : SchemeBaseChange S) where
  /-- The triple product `X ×_S Y ×_S W`. -/
  triple : SchemeBaseChange S
  /-- Projection to `X ×_S Y`. -/
  πXY : triple ⟶ Z₁
  /-- Projection to `Y ×_S W`. -/
  πYW : triple ⟶ Z₂
  /-- Projection to `X ×_S W`, along which the convolution is pushed. -/
  πXW : triple ⟶ Z₃

end TripleProduct

section Convolution

variable {Z₁ Z₂ Z₃ : SchemeBaseChange S}
  [IsLocallyNoetherian Z₁.left] [IsLocallyNoetherian Z₂.left]
  [IsLocallyNoetherian Z₃.left]
  (G : TripleProductGeometry Z₁ Z₂ Z₃) [IsLocallyNoetherian G.triple.left]

/-- **The convolution of two kernels — a definition, not supplied data.**

`conv P Q = Rπ_{XW*}(π_{XY}^* P ⊗^L π_{YW}^* Q)`, the classical formula, built
from functors the first ledger already names. This is the field that
`ConvolutionData` asks for as data and that this ledger removes from the
obligation list. -/
noncomputable def convKernel
    [HasCoherentPullback G.πXY] [HasCoherentPullback G.πYW]
    [HasDerivedTensor G.triple] [HasDerivedPushforward G.πXW]
    (P : SchemeBoundedCoherentDerivedCategory Z₁.left)
    (Q : SchemeBoundedCoherentDerivedCategory Z₂.left) :
    SchemeBoundedCoherentDerivedCategory Z₃.left :=
  (derivedPushforward G.πXW).obj
    (((derivedTensor G.triple).obj
        ((boundedCoherentDerivedPullback G.πYW).obj Q)).obj
      ((boundedCoherentDerivedPullback G.πXY).obj P))

end Convolution

section ClassicalInputs

variable {Z : SchemeBaseChange S} [IsLocallyNoetherian Z.left]

/-- **The projection formula, supplied.**

`Rq_*(A ⊗^L Lq^* B) ≅ Rq_* A ⊗^L B`, for `q : Z ⟶ U`.

Named because it is one of the two classical inputs to Prop. 5.10, **not**
because anything in this file uses it. Nothing here derives `compIso`, and this
class is not a step toward it — it is a statement of what such a step would
need. -/
class HasProjectionFormula {Z U : SchemeBaseChange S}
    [IsLocallyNoetherian Z.left] [IsLocallyNoetherian U.left] (q : Z ⟶ U)
    [HasCoherentPullback q] [HasDerivedTensor Z] [HasDerivedTensor U]
    [HasDerivedPushforward q] where
  /-- The projection isomorphism, natural in both arguments. -/
  iso : ∀ B : SchemeBoundedCoherentDerivedCategory U.left,
    (derivedTensor Z).obj ((boundedCoherentDerivedPullback q).obj B) ⋙
        derivedPushforward q ≅
      derivedPushforward q ⋙ (derivedTensor U).obj B

/-- **Flat base change, supplied.**

For a cartesian square with `u`, `v` the two sides and `p`, `q` the two
projections, `Lv^* Rq_* ≅ Rq'_* Lu^*`.

The square this file has in mind is the one formed by two projections of the
triple product, which is cartesian *because* the objects are products — the
place where productness finally does work. Stated abstractly on a supplied
square so that the class does not itself have to assert productness.

Named, not used: as with `HasProjectionFormula`, nothing here derives anything
from it. -/
class HasFlatBaseChange {T T' U U' : SchemeBaseChange S}
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian T'.left]
    [IsLocallyNoetherian U.left] [IsLocallyNoetherian U'.left]
    (q : T ⟶ U) (q' : T' ⟶ U') (u : T' ⟶ T) (v : U' ⟶ U)
    [HasCoherentPullback u] [HasCoherentPullback v]
    [HasDerivedPushforward q] [HasDerivedPushforward q'] where
  /-- The square commutes. -/
  comm : u ≫ q = q' ≫ v
  /-- Base-change isomorphism. -/
  iso : derivedPushforward q ⋙ boundedCoherentDerivedPullback v ≅
    boundedCoherentDerivedPullback u ⋙ derivedPushforward q'

end ClassicalInputs

section Assembly

variable {X Y W Z₁ Z₂ Z₃ : SchemeBaseChange S}
  [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left]
  [IsLocallyNoetherian W.left] [IsLocallyNoetherian Z₁.left]
  [IsLocallyNoetherian Z₂.left] [IsLocallyNoetherian Z₃.left]

/-- **The remaining obligation: Prop. 5.10 for the geometric convolution.**

`Φ_P ⋙ Φ_Q ≅ Φ_{convKernel P Q}`, uniformly in `Q`.

This is the one field of `ConvolutionData` that survives the ledger. It is a
real theorem, not bookkeeping, and proving it is where the geometry finally has
to be done: the classical argument pushes the composite around the triple
product using the **projection formula** and **flat base change**, and the
base-change square it uses is cartesian precisely because the intermediate
objects are honest fibre products.

So a caller discharging this class is asserting the product structure, whether
or not it is spelled out — which is why neither this file nor
`KernelCorrespondence.lean` asserts it separately. `HasProjectionFormula` and
`HasFlatBaseChange` are named above as what a proof would consume; nothing here
consumes them. -/
class HasConvolutionComparison
    (p₁ : Z₁ ⟶ X) (q₁ : Z₁ ⟶ Y) (p₂ : Z₂ ⟶ Y) (q₂ : Z₂ ⟶ W)
    (p₃ : Z₃ ⟶ X) (q₃ : Z₃ ⟶ W)
    [HasCoherentPullback p₁] [HasDerivedTensor Z₁] [HasDerivedPushforward q₁]
    [HasCoherentPullback p₂] [HasDerivedTensor Z₂] [HasDerivedPushforward q₂]
    [HasCoherentPullback p₃] [HasDerivedTensor Z₃] [HasDerivedPushforward q₃]
    (G : TripleProductGeometry Z₁ Z₂ Z₃) [IsLocallyNoetherian G.triple.left]
    [HasCoherentPullback G.πXY] [HasCoherentPullback G.πYW]
    [HasDerivedTensor G.triple] [HasDerivedPushforward G.πXW] where
  /-- Prop. 5.10, uniformly in both kernels. -/
  compIso : ∀ (P : SchemeBoundedCoherentDerivedCategory Z₁.left)
      (Q : SchemeBoundedCoherentDerivedCategory Z₂.left),
    (geometricCorrespondence X Y Z₁ p₁ q₁).transform P ⋙
        (geometricCorrespondence Y W Z₂ p₂ q₂).transform Q ≅
      (geometricCorrespondence X W Z₃ p₃ q₃).transform (convKernel G P Q)

/-- **The geometric convolution data, assembled.**

A `ConvolutionData` for the three geometric correspondences, with `conv` the
*constructed* `convKernel` and `compIso` the one remaining supplied field.

Compare the abstract structure, which asks for both. That is the whole content
of this ledger. -/
noncomputable def geometricConvolutionData
    (p₁ : Z₁ ⟶ X) (q₁ : Z₁ ⟶ Y) (p₂ : Z₂ ⟶ Y) (q₂ : Z₂ ⟶ W)
    (p₃ : Z₃ ⟶ X) (q₃ : Z₃ ⟶ W)
    [HasCoherentPullback p₁] [HasDerivedTensor Z₁] [HasDerivedPushforward q₁]
    [HasCoherentPullback p₂] [HasDerivedTensor Z₂] [HasDerivedPushforward q₂]
    [HasCoherentPullback p₃] [HasDerivedTensor Z₃] [HasDerivedPushforward q₃]
    (G : TripleProductGeometry Z₁ Z₂ Z₃) [IsLocallyNoetherian G.triple.left]
    [HasCoherentPullback G.πXY] [HasCoherentPullback G.πYW]
    [HasDerivedTensor G.triple] [HasDerivedPushforward G.πXW]
    [HasConvolutionComparison p₁ q₁ p₂ q₂ p₃ q₃ G] :
    ConvolutionData (geometricCorrespondence X Y Z₁ p₁ q₁)
      (geometricCorrespondence Y W Z₂ p₂ q₂)
      (geometricCorrespondence X W Z₃ p₃ q₃) where
  conv P Q := convKernel G P Q
  compIso P Q := HasConvolutionComparison.compIso P Q

end Assembly

/-! ## What the two ledgers together leave

For a geometric Fourier--Mukai theory with composition, a caller must supply:

1. `HasDerivedTensor` on each of the four relevant schemes — absent from the
   repository;
2. `HasDerivedPushforward` along each of the four relevant morphisms — absent
   from the repository, and where properness lives;
3. `HasCoherentPullback` along each pullback used — an *existing* contract from
   #460--462, so no new kind of obligation;
4. a `TripleProductGeometry` — the objects and projections;
5. `HasConvolutionComparison` — Prop. 5.10, the one genuine theorem left, whose
   proof needs the projection formula and flat base change (both named above)
   and the product structure.

Everything else in the Fourier--Mukai lane follows: `transform`,
`transformK₀`, closure of kernel functors under composition, the transport of
stability conditions, and — with a `KernelAutoequivalence` and a `DualKernel`
on top — the group action and the Mukai isometry.

Still unreachable geometrically, and not addressed by either ledger:
`UnitKernelData` (needs `𝒪_Δ`), `DualKernel` (needs `P^∨ ⊗ p^*ω[dim]`), and
associativity of convolution (needs a second comparison layer).
-/

end CategoryTheory.Triangulated.StabilityCondition.Families
