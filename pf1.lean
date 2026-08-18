import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Affine.Comparison
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

noncomputable example (M : (Spec S).Modules) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj M) ≅
      (ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj M) :=
  (TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
      (CategoryTheory.evaluation _ _).obj (op (⊤ : (Spec R).Opens))).mapIso
    ((AlgebraicGeometry.pushforwardCompModulesSpecToSheafIso φ).app M)
