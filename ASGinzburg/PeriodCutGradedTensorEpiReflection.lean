import ASGinzburg.PeriodCutOrdinaryGradedNakayama
import ASGinzburg.GradedCokernelFunctorEpiReflection
import ASGinzburg.BalancedTensorLeftAdjunction

/-! The genuine native semisimple tensor functor reflects epimorphisms
of grade-preserving ordinary right-module maps with bounded target. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cutGradedTensor_epi_reflect
    (P M : GradedOrdinaryModuleData k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))ᵐᵒᵖ
      (E.cutIntegerOppositeHomogeneousSpace Q))
    (b : ℤ) (hb : M.BoundedBelow b)
    (f : P.ringModule ⟶ M.ringModule) (hf : P.PreservesGrade M f)
    [Epi ((balancedTensorLeftFunctor k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q)).map f)] :
    Epi f := by
  have hDetect : ∀ N : GradedOrdinaryModuleData k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))ᵐᵒᵖ
      (E.cutIntegerOppositeHomogeneousSpace Q), N.BoundedBelow b →
      IsZero ((balancedTensorLeftFunctor k
        (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))
        (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q)).obj
        N.ringModule) → IsZero N.ringModule :=
    fun N hN hT => E.ordinaryGradedData_isZero_of_tensor_semisimple Q N b hN hT
  exact gradedMap_epi_of_functor_epi
    (balancedTensorLeftFunctor k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q))
    hDetect P M hb f hf

end ASGinzburg.ZAlgebra.PeriodIso
