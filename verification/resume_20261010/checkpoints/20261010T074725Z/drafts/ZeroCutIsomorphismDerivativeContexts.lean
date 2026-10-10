import work.ASGinzburgDraft.ZeroCutJacobianIsomorphismPathLift
import work.ASGinzburgDraft.NoncutJacobianContextCoefficients
import ASGinzburg.ZeroCutJacobianRing

/-! The actual noncut lift of a genuine native Jacobian isomorphism
expresses each original cut derivative in finite genuine target contexts. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]
variable {φ ψ : Q.Potential k}
variable (F : ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ)
  (Q.unrolledJacobianZAlgebra k ψ))

noncomputable def zeroCutIsomorphismDerivativeImage (a : {a : Q.Arrow // Q.cut a = true}) :
    Q.pathCutComponent k (Q.target a.val) (Q.source a.val) 0 :=
  VertexCutPathAutomorphism.cutComponentLinearEquiv Q k
    (Q.zeroCutIsomorphismPathAutomorphism k F) _ _ 0 (Q.zeroCutCyclicDerivative k φ a)

theorem zeroCutIsomorphismDerivativeImage_mem (a : {a : Q.Arrow // Q.cut a = true}) :
    (Q.zeroCutIsomorphismDerivativeImage k F a).val ∈
      (Q.pathJacobianIdeal k ψ).hom (Q.target a.val) (Q.source a.val) :=
  (Q.zeroCutIsomorphismPathAutomorphism_jacobian_mem_iff k F _ _
    (Q.zeroCutCyclicDerivative k φ a)).mpr (Q.pathCyclicDerivative_mem_pathJacobianIdeal k φ a.val)

noncomputable def zeroCutIsomorphismDerivativeContextCoefficients
    (a : {a : Q.Arrow // Q.cut a = true}) :
    Q.NoncutJacobianContextIndex (Q.target a.val) (Q.source a.val) →₀ k :=
  Q.noncutJacobianContextCoefficients k ψ _ _ (Q.zeroCutIsomorphismDerivativeImage k F a)
    (Q.zeroCutIsomorphismDerivativeImage_mem k F a)

theorem zeroCutIsomorphismDerivativeContextCoefficients_expansion
    (a : {a : Q.Arrow // Q.cut a = true}) :
    Q.noncutJacobianContextLinearMap k ψ (Q.target a.val) (Q.source a.val)
      (Q.zeroCutIsomorphismDerivativeContextCoefficients k F a) =
        (Q.zeroCutIsomorphismDerivativeImage k F a).val :=
  Q.noncutJacobianContextCoefficients_expansion k ψ _ _
    (Q.zeroCutIsomorphismDerivativeImage k F a) (Q.zeroCutIsomorphismDerivativeImage_mem k F a)

end ASGinzburg.CutQuiver
