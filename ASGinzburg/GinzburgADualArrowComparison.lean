import ASGinzburg.GinzburgOppositeArrowProducts
import ASGinzburg.GinzburgEndpointCoordinateValues
import ASGinzburg.GinzburgFirstADualFormula
import ASGinzburg.GinzburgProjectiveCoordinateFormulas

/-! The genuine first and third canonical A-dual differentials are the
actual opposite native third and first differentials on every Hom element. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k] (φ : Q.Potential k)

theorem ginzburgOriginalRepresentableProjectiveMap_adual_opposite (v l : Q.LiftVertex)
    (f : (Q.unrolledJacobianZAlgebra k φ).representable (Q.height v) ⟶
      (Q.unrolledJacobianZAlgebra k φ).representable (Q.height l)) :
    Q.ginzburgOriginalADualOppositeComponentEquiv k φ v l
      (((Q.unrolledJacobianZAlgebra k φ).rightModuleADualMap
        (Q.ginzburgOriginalRepresentableProjectiveMap k φ v)).app ⟨Q.height l⟩ f)=
      ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).rightModuleEvaluation
        (Q.opposite.height (Q.oppositeLiftVertexEquiv l))).map
        (Q.opposite.ginzburgLoopDualProjectiveMap k (Q.oppositePotentialEquiv k φ)
          (Q.ginzburgDualOppositeBase v))
        (Q.ginzburgRepresentableADualOppositeLoopComponentEquiv k φ v l f) := by
  classical
  apply ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).ginzburgGeneratorCoefficientComponentEquiv Q.opposite (Q.ginzburgDualOppositeBase v) (-1)
      (Q.opposite.height (Q.oppositeLiftVertexEquiv l))).injective
  funext c
  obtain ⟨a,rfl⟩ := (Q.ginzburgOriginalOppositeDualEquiv v).surjective c
  rw [Q.ginzburgOriginalADualOppositeComponentEquiv_coefficients,
    Q.opposite.ginzburgLoopDualProjectiveMap_coordinates,
    Q.ginzburgOriginalOppositeCoefficientEquiv_apply,
    Q.ginzburgOriginalRepresentableProjectiveMap_adual_matrix]
  rw [←(Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).ginzburgLoopCoefficientEvaluationEquiv_apply,
    Q.ginzburgRepresentableADualOppositeLoopComponentEquiv_coordinate]
  exact Q.ginzburgOppositeOriginalArrowProduct k φ v l a _

theorem ginzburgLoopDualProjectiveMap_adual_opposite (v l : Q.LiftVertex)
    (f : (Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v (-1) ⟶
      (Q.unrolledJacobianZAlgebra k φ).representable (Q.height l)) :
    Q.ginzburgLoopADualOppositeRepresentableComponentEquiv k φ v l
      (((Q.unrolledJacobianZAlgebra k φ).rightModuleADualMap
        (Q.ginzburgLoopDualProjectiveMap k φ v)).app ⟨Q.height l⟩ f)=
      ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).rightModuleEvaluation
        (Q.opposite.height (Q.oppositeLiftVertexEquiv l))).map
        (Q.opposite.ginzburgOriginalRepresentableProjectiveMap k (Q.oppositePotentialEquiv k φ)
          (Q.ginzburgDualOppositeBase v))
        (Q.ginzburgDualADualOppositeComponentEquiv k φ v l f) := by
  classical
  rw [Q.ginzburgLoopDualProjectiveMap_adual_opposite_coordinates,
    Q.opposite.ginzburgOriginalRepresentableProjectiveMap_coordinates]
  rw [Q.ginzburgDualADualOppositeComponentEquiv_coefficients]
  conv_rhs => rw [←(Q.ginzburgDualOppositeOriginalEquiv v).sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [Q.ginzburgDualOppositeCoefficientEquiv_apply]
  exact Q.ginzburgOppositeLoopArrowProduct k φ v l a _

end ASGinzburg.CutQuiver
