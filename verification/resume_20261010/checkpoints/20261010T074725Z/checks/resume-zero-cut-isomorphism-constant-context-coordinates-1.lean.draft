import work.ASGinzburgDraft.ZeroCutIsomorphismDerivativeBasisTransport
import work.ASGinzburgDraft.NoncutJacobianContextNativeExpansion
import work.ASGinzburgDraft.ZeroCutIsomorphismDerivativeContexts

set_option synthInstance.maxHeartbeats 200000

/-! The actual constant coefficients of the actual context expansion
are exactly the native derivative-basis coordinates of the genuine
minimal-relation equivalence. Invertibility follows from that equivalence. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]
variable {φ ψ : Q.Potential k}
variable (F : ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ)
  (Q.unrolledJacobianZAlgebra k ψ))

theorem zeroCutIsomorphismDerivativeImage_minimalClass
    (a : {a : Q.Arrow // Q.cut a = true}) :
    Q.zeroCutIsomorphismMinimalRelationEquiv k F (Q.target a.val) (Q.source a.val)
      (Q.foundationMinimalCutDerivativeClass k φ (Q.target a.val) (Q.source a.val)
        ⟨a.val, rfl, rfl, a.property⟩) =
    Submodule.Quotient.mk (Q.zeroCutJacobianRelationNativeElement k ψ (Q.target a.val)
      (Q.source a.val) (Q.zeroCutIsomorphismDerivativeImage k F a)
        (Q.zeroCutIsomorphismDerivativeImage_mem k F a)) := by
  unfold foundationMinimalCutDerivativeClass generatedMinimalRelationClass
  rw [Q.zeroCutIsomorphismMinimalRelationEquiv_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  rw [Q.zeroCutIsomorphismJacobianComponentLinearEquiv_val]
  change VertexCutPathAutomorphism.foundationPathComponentLinearEquiv Q k
    (Q.zeroCutIsomorphismPathAutomorphism k F) _ _
      (Q.foundationCutDerivativeGenerator k φ (Q.target a.val) (Q.source a.val)
        ⟨a.val, rfl, rfl, a.property⟩).val =
    Q.zeroCutFoundationComponentEquiv k (Q.target a.val) (Q.source a.val)
      (Q.zeroCutIsomorphismDerivativeImage k F a)
  rw [← Q.zeroCutFoundationComponentEquiv_cutDerivative k φ a]
  exact VertexCutPathAutomorphism.foundationPathComponentLinearEquiv_on_cut Q k _ _ _ _

theorem zeroCutIsomorphismDerivativeImage_constantCoordinates
    (hψ : Q.GinzburgRegular k ψ) (a : {a : Q.Arrow // Q.cut a = true}) :
    (hψ.foundationCutDerivativeMinimalRelationBasis Q k (Q.target a.val) (Q.source a.val)).repr
      (Q.zeroCutIsomorphismMinimalRelationEquiv k F (Q.target a.val) (Q.source a.val)
        (Q.foundationMinimalCutDerivativeClass k φ (Q.target a.val) (Q.source a.val)
          ⟨a.val, rfl, rfl, a.property⟩)) =
    Q.noncutJacobianContextConstantProjection k (Q.target a.val) (Q.source a.val)
      (Q.zeroCutIsomorphismDerivativeContextCoefficients k F a) := by
  rw [Q.zeroCutIsomorphismDerivativeImage_minimalClass,
    Q.zeroCutJacobianRelationNativeElement_minimalClass]
  have hb : Q.foundationMinimalCutDerivativeClass k ψ (Q.target a.val) (Q.source a.val) =
      hψ.foundationCutDerivativeMinimalRelationBasis Q k (Q.target a.val) (Q.source a.val) := by
    funext b
    exact (hψ.foundationCutDerivativeMinimalRelationBasis_apply Q k _ _ b).symm
  rw [hb, Module.Basis.repr_linearCombination]
  rfl

theorem zeroCutIsomorphismDerivativeCoordinateEquiv_constantProjection
    (hφ : Q.GinzburgRegular k φ) (hψ : Q.GinzburgRegular k ψ)
    (a : {a : Q.Arrow // Q.cut a = true}) :
    Q.zeroCutIsomorphismDerivativeCoordinateEquiv k F hφ hψ (Q.target a.val) (Q.source a.val)
      (Finsupp.single (⟨a.val, rfl, rfl, a.property⟩ :
        Q.FoundationRelationArrow (Q.target a.val) (Q.source a.val)) 1) =
    Q.noncutJacobianContextConstantProjection k (Q.target a.val) (Q.source a.val)
      (Q.zeroCutIsomorphismDerivativeContextCoefficients k F a) := by
  rw [Q.zeroCutIsomorphismDerivativeCoordinateEquiv_single]
  exact Q.zeroCutIsomorphismDerivativeImage_constantCoordinates k F hψ a

end ASGinzburg.CutQuiver
