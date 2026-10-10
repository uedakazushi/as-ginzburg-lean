import ASGinzburg.ASFoundationRelationDescent
import work.ASGinzburgDraft.QuotientBasisRepresentativeIndependence

/-! The actual representatives used by the foundation construction
are linearly independent because their quotient classes are a basis. -/
namespace ASGinzburg.CutQuiver
universe u w
variable (Q : CutQuiver) {k : Type u} [Field k]
  (I : (Q.unrolledPathZAlgebra k).LinearIdeal) (i j : ℤ)

theorem minimalRelationBasisLift_linearIndependent {ι : Type w}
    (b : Module.Basis ι k (Q.MinimalRelationComponent I i j)) :
    LinearIndependent k (Q.minimalRelationBasisLift I i j b) := by
  let result := quotientBasisRepresentatives_linearIndependent
    (Submodule.comap (I.hom i j).subtype (Q.relationDecomposables I i j)) b
    (Q.minimalRelationBasisLift I i j b) (Q.minimalRelationBasisLift_class I i j b)
  exact result

end ASGinzburg.CutQuiver

namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.foundationRelationLift_linearIndependent (hAS : A.ASRegular Q)
    (i j : Q.Vertex) :
    LinearIndependent k (hAS.foundationRelationLift A Q i j) :=
  Q.minimalRelationBasisLift_linearIndependent _ _ _ (hAS.foundationMinimalRelationBasis A Q i j)

theorem ASRegular.foundationRelationNative_linearIndependent (hAS : A.ASRegular Q)
    (i j : Q.Vertex) :
    LinearIndependent k (hAS.foundationRelationNative A Q i j) := by
  apply LinearIndependent.of_comp
    (A.pathRelationHeightEquiv Q (hAS.resolution A Q) (i,0) (j,0)).toLinearMap
  have h : (A.pathRelationHeightEquiv Q (hAS.resolution A Q) (i,0) (j,0)).toLinearMap ∘
      hAS.foundationRelationNative A Q i j = hAS.foundationRelationLift A Q i j := by
    funext a
    apply Subtype.ext
    exact hAS.foundationRelationNative_height A Q i j a
  rw [h]
  exact hAS.foundationRelationLift_linearIndependent A Q i j

theorem ASRegular.foundationPathRelation_linearIndependent (hAS : A.ASRegular Q)
    (i j : Q.Vertex) :
    LinearIndependent k (hAS.foundationPathRelation A Q i j) := by
  have h := (hAS.foundationRelationNative_linearIndependent A Q i j).map'
    (LinearMap.ker (A.unrolledPathLinearEvaluation Q (hAS.resolution A Q) (i,0) (j,0))).subtype
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have he := h.map' (Q.unrolledPathEraseLinearMap k (i,0) (j,0))
    (LinearMap.ker_eq_bot.mpr (Q.unrolledPathEraseLinearMap_injective k (i,0) (j,0)))
  exact he

end ASGinzburg.ZAlgebra
