import ASGinzburg.ASResolution

/-! Actual object isomorphisms in the right module category preserve
zero composites, exactness, and the positive-action notion of minimality. -/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def conjugateRightModuleMap {M N M' N' : A.RightModule}
    (eM : M ≅ M') (eN : N ≅ N') (f : M ⟶ N) : M' ⟶ N' :=
  eM.inv ≫ f ≫ eN.hom

theorem conjugateRightModuleMap_comp_zero {M N P M' N' P' : A.RightModule}
    (eM : M ≅ M') (eN : N ≅ N') (eP : P ≅ P')
    (f : M ⟶ N) (g : N ⟶ P) (h : f ≫ g = 0) :
    A.conjugateRightModuleMap eM eN f ≫ A.conjugateRightModuleMap eN eP g = 0 := by
  simp only [conjugateRightModuleMap, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc f, h, zero_comp, comp_zero]

noncomputable def conjugateRightModuleShortComplexIso (S : ShortComplex A.RightModule)
    {M' N' P' : A.RightModule} (eM : S.X₁ ≅ M') (eN : S.X₂ ≅ N') (eP : S.X₃ ≅ P') :
    S ≅ ShortComplex.mk (A.conjugateRightModuleMap eM eN S.f)
      (A.conjugateRightModuleMap eN eP S.g)
      (A.conjugateRightModuleMap_comp_zero eM eN eP S.f S.g S.zero) :=
  ShortComplex.isoMk eM eN eP
    (by simp only [conjugateRightModuleMap, Iso.hom_inv_id_assoc])
    (by simp only [conjugateRightModuleMap, Iso.hom_inv_id_assoc])

theorem conjugateRightModuleShortComplex_exact (S : ShortComplex A.RightModule) (h : S.Exact)
    {M' N' P' : A.RightModule} (eM : S.X₁ ≅ M') (eN : S.X₂ ≅ N') (eP : S.X₃ ≅ P') :
    (ShortComplex.mk (A.conjugateRightModuleMap eM eN S.f)
      (A.conjugateRightModuleMap eN eP S.g)
      (A.conjugateRightModuleMap_comp_zero eM eN eP S.f S.g S.zero)).Exact :=
  ShortComplex.exact_of_iso (A.conjugateRightModuleShortComplexIso S eM eN eP) h

theorem conjugateRightModuleMap_minimal {M N M' N' : A.RightModule}
    (eM : M ≅ M') (eN : N ≅ N') (f : M ⟶ N) (hf : A.IsMinimalMorphism f) :
    A.IsMinimalMorphism (A.conjugateRightModuleMap eM eN f) :=
  A.isMinimalMorphism_comp_left eM.inv (f ≫ eN.hom)
    (A.isMinimalMorphism_comp_right f eN.hom hf)

end ASGinzburg.ZAlgebra
