/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Convolution
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.GrothendieckGroup

/-! # Fourier--Mukai transforms

Kernel functors between triangulated categories, stated for an abstract
correspondence; the convolution of kernels as supplied data; and the induced
maps on the triangulated Grothendieck group.  No geometry, and no theorem
asserting that a functor is of this form.

`Basic` and `Convolution` depend on Mathlib alone.  `GrothendieckGroup` is the
only module here that reaches into `StabilityCondition.Foundation`, for `K₀`.
-/
