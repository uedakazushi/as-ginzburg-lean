import ASGinzburg.GinzburgAugmentationHeightHomology
import ASGinzburg.RepresentableRadicalComponents
import ASGinzburg.JacobianUnrollingQuotient

/-! Actual augmentation homology identifies with the existing radical
component. This comparison requires no Ginzburg regularity hypothesis. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgAugmentationRadicalComponentIso (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    Q.ginzburgAugmentationHomology k φ x.1 v.1 (v.2-x.2) 0 ≅
      ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).representableRadical (Q.height v)).object := by
  by_cases h : Q.height x<Q.height v
  · exact Q.ginzburgAugmentationHeightHomologyIso k φ x v h 0 ≪≫
      Q.ginzburgCutHomologyZeroUnrolledIso k φ x v ≪≫
        ((Q.unrolledJacobianZAlgebra k φ).representableRadicalBelowComponentIso
          (Q.height x) (Q.height v) h).symm
  · exact (Q.ginzburgAugmentationHomology_isZero_of_not_height_lt k φ x v 0 h).isoZero ≪≫
      ((Q.unrolledJacobianZAlgebra k φ).representableRadicalComponent_isZero_of_not_lt
        (Q.height x) (Q.height v) h).isoZero.symm

end ASGinzburg.CutQuiver
