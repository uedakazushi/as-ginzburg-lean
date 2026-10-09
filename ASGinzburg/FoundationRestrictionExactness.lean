import ASGinzburg.FoundationRightRestriction
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! Sheet-zero restriction preserves actual kernels, cokernels, homology
and exact sequences in the original linear module model. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe u v w w'
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable instance foundationRestrictionPreservesLimitsOfShape
    (J : Type w) [Category.{w'} J] [HasLimitsOfShape J (ModuleCat.{v} k)] :
    PreservesLimitsOfShape J (A.foundationRestriction Q) := by
  haveI : PreservesLimitsOfShape J (A.foundationRestriction Q ⋙
      (linearPresheafProperty k (A.FoundationRightObj Q)).ι) := by
    change PreservesLimitsOfShape J (A.rightModuleProperty.ι ⋙
      (whiskeringLeft (A.FoundationRightObj Q) A.Objᵒᵖ (ModuleCat.{v} k)).obj
        (A.foundationRightInclusion Q))
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves (A.foundationRestriction Q)
    (linearPresheafProperty k (A.FoundationRightObj Q)).ι

noncomputable instance foundationRestrictionPreservesColimitsOfShape
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J (ModuleCat.{v} k)] :
    PreservesColimitsOfShape J (A.foundationRestriction Q) := by
  haveI : PreservesColimitsOfShape J (A.foundationRestriction Q ⋙
      (linearPresheafProperty k (A.FoundationRightObj Q)).ι) := by
    change PreservesColimitsOfShape J (A.rightModuleProperty.ι ⋙
      (whiskeringLeft (A.FoundationRightObj Q) A.Objᵒᵖ (ModuleCat.{v} k)).obj
        (A.foundationRightInclusion Q))
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves (A.foundationRestriction Q)
    (linearPresheafProperty k (A.FoundationRightObj Q)).ι

noncomputable instance foundationRestrictionPreservesFiniteLimits :
    PreservesFiniteLimits (A.foundationRestriction Q) where
  preservesFiniteLimits _ := inferInstance

noncomputable instance foundationRestrictionPreservesFiniteColimits :
    PreservesFiniteColimits (A.foundationRestriction Q) where
  preservesFiniteColimits _ := inferInstance

noncomputable instance foundationRestrictionPreservesHomology :
    (A.foundationRestriction Q).PreservesHomology := by infer_instance

noncomputable def foundationRestrictionKernelIso {M N : A.RightModule} (f : M ⟶ N) :
    (A.foundationRestriction Q).obj (kernel f) ≅
      kernel ((A.foundationRestriction Q).map f) :=
  PreservesKernel.iso (A.foundationRestriction Q) f

noncomputable def foundationRestrictionCokernelIso {M N : A.RightModule} (f : M ⟶ N) :
    (A.foundationRestriction Q).obj (cokernel f) ≅
      cokernel ((A.foundationRestriction Q).map f) :=
  PreservesCokernel.iso (A.foundationRestriction Q) f

theorem foundationRestriction_exact (S : ShortComplex A.RightModule) (hS : S.Exact) :
    (S.map (A.foundationRestriction Q)).Exact := hS.map (A.foundationRestriction Q)

theorem foundationRestriction_shortExact (S : ShortComplex A.RightModule)
    (hS : S.ShortExact) :
    (S.map (A.foundationRestriction Q)).ShortExact := hS.map_of_exact (A.foundationRestriction Q)

end ASGinzburg.ZAlgebra
