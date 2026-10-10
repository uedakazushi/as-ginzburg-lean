import work.ASGinzburgDraft.TriangleASIncomingArrowBasis
import work.ASGinzburgDraft.TriangleJacobianArrowQuotients
import ASGinzburg.ZeroCutUnrollingProducts
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The chosen AS path presentation supplies genuine invertible X/Y
evaluation maps, using actual path evaluation rather than assumed bases. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def ASRegular.triangleXArrowEvaluation (hAS : A.ASRegular triangle333) :
    ArrowSpace333 k →ₗ[k] A.Hom 0 1 :=
  (A.unrolledPathLinearEvaluation triangle333 (hAS.resolution A triangle333) (0,0) (1,0)).comp
    ((triangle333.zeroCutNativeUnrollingEquiv k 0 1).toLinearMap.comp
      (triangleXArrowCutEquiv k).toLinearMap)

noncomputable def ASRegular.triangleYArrowEvaluation (hAS : A.ASRegular triangle333) :
    ArrowSpace333 k →ₗ[k] A.Hom 1 2 :=
  (A.unrolledPathLinearEvaluation triangle333 (hAS.resolution A triangle333) (1,0) (2,0)).comp
    ((triangle333.zeroCutNativeUnrollingEquiv k 1 2).toLinearMap.comp
      (triangleYArrowCutEquiv k).toLinearMap)

theorem ASRegular.triangleXArrowEvaluation_bijective (hAS : A.ASRegular triangle333) :
    Function.Bijective (hAS.triangleXArrowEvaluation A) := by
  have hs : Function.Surjective (hAS.triangleXArrowEvaluation A) :=
    (A.unrolledPathLinearEvaluation_surjective triangle333 (hAS.resolution A triangle333)
      (0,0) (1,0)).comp ((triangle333.zeroCutNativeUnrollingEquiv k 0 1).surjective.comp
        (triangleXArrowCutEquiv k).surjective)
  have hr : Module.finrank k (A.Hom 0 1) = 3 := by
    exact Module.finrank_eq_card_basis
      ((hAS.resolution A triangle333 (1,0)).triangleAdjacentIncomingBasis)
  have hd : Module.finrank k (ArrowSpace333 k) = Module.finrank k (A.Hom 0 1) := by
    rw [hr]
    simp [ArrowSpace333]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hs, hs⟩

theorem ASRegular.triangleYArrowEvaluation_bijective (hAS : A.ASRegular triangle333) :
    Function.Bijective (hAS.triangleYArrowEvaluation A) := by
  have hs : Function.Surjective (hAS.triangleYArrowEvaluation A) :=
    (A.unrolledPathLinearEvaluation_surjective triangle333 (hAS.resolution A triangle333)
      (1,0) (2,0)).comp ((triangle333.zeroCutNativeUnrollingEquiv k 1 2).surjective.comp
        (triangleYArrowCutEquiv k).surjective)
  have hr : Module.finrank k (A.Hom 1 2) = 3 := by
    exact Module.finrank_eq_card_basis
      ((hAS.resolution A triangle333 (2,0)).triangleAdjacentIncomingBasis)
  have hd : Module.finrank k (ArrowSpace333 k) = Module.finrank k (A.Hom 1 2) := by
    rw [hr]
    simp [ArrowSpace333]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hs, hs⟩

noncomputable def ASRegular.triangleXArrowEvaluationEquiv (hAS : A.ASRegular triangle333) :
    ArrowSpace333 k ≃ₗ[k] A.Hom 0 1 :=
  LinearEquiv.ofBijective (hAS.triangleXArrowEvaluation A) (hAS.triangleXArrowEvaluation_bijective A)

noncomputable def ASRegular.triangleYArrowEvaluationEquiv (hAS : A.ASRegular triangle333) :
    ArrowSpace333 k ≃ₗ[k] A.Hom 1 2 :=
  LinearEquiv.ofBijective (hAS.triangleYArrowEvaluation A) (hAS.triangleYArrowEvaluation_bijective A)

noncomputable def ASRegular.triangleXYPathEvaluation (hAS : A.ASRegular triangle333) :
    triangle333.pathCutComponent k 0 2 0 →ₗ[k] A.Hom 0 2 :=
  (A.unrolledPathLinearEvaluation triangle333 (hAS.resolution A triangle333) (0,0) (2,0)).comp
    (triangle333.zeroCutNativeUnrollingEquiv k 0 2).toLinearMap

theorem ASRegular.triangleXYPathEvaluation_comp (hAS : A.ASRegular triangle333)
    (x y : ArrowSpace333 k) :
    hAS.triangleXYPathEvaluation A (triangle333.zeroCutPathComp k
      (triangleYArrowCutEquiv k y) (triangleXArrowCutEquiv k x)) =
      A.comp (hAS.triangleYArrowEvaluation A y) (hAS.triangleXArrowEvaluation A x) := by
  change A.unrolledPathLinearEvaluation triangle333 (hAS.resolution A triangle333) (0,0) (2,0)
    (triangle333.zeroCutNativeUnrollingEquiv k 0 2
      (triangle333.zeroCutPathComp k (triangleYArrowCutEquiv k y) (triangleXArrowCutEquiv k x))) = _
  rw [triangle333.zeroCutNativeUnrollingEquiv_comp,
    A.unrolledPathLinearEvaluation_comp]
  rfl

end ASGinzburg.ZAlgebra
