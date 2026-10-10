import work.ASGinzburgDraft.ZeroCutIsomorphismConstantContextCoordinates

/-! Endpoint-typed actual constant context coefficients coincide with
the genuine transpose coordinate equivalence on the actual cut block. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]
variable {φ ψ : Q.Potential k}
variable (F : ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ)
  (Q.unrolledJacobianZAlgebra k ψ))

theorem zeroCutIsomorphismDerivativeTransposeEquiv_coeff_transport
    (hφ : Q.GinzburgRegular k φ) (hψ : Q.GinzburgRegular k ψ)
    {i j i' j' : Q.Vertex} (hi : i = i') (hj : j = j')
    (b a : Q.FoundationRelationArrow i j) :
    Q.zeroCutIsomorphismDerivativeTransposeEquiv k F hφ hψ i j (Finsupp.single b 1) a =
    Q.zeroCutIsomorphismDerivativeTransposeEquiv k F hφ hψ i' j'
      (Finsupp.single (⟨b.val, b.property.1.trans hj,
        b.property.2.1.trans hi, b.property.2.2⟩ : Q.FoundationRelationArrow i' j') 1)
      ⟨a.val, a.property.1.trans hj, a.property.2.1.trans hi, a.property.2.2⟩ := by
  subst i' j'
  rfl

theorem zeroCutIsomorphismTransposedConstantCoefficient
    (hφ : Q.GinzburgRegular k φ) (hψ : Q.GinzburgRegular k ψ)
    (b : Q.Arrow) (hb : Q.cut b = true)
    (a : Q.FoundationRelationArrow (Q.target b) (Q.source b)) :
    Q.noncutJacobianContextConstantProjection k (Q.target a.val) (Q.source a.val)
      (Q.zeroCutIsomorphismDerivativeContextCoefficients k F ⟨a.val, a.property.2.2⟩)
      ⟨b, a.property.1.symm, a.property.2.1.symm, hb⟩ =
    Q.zeroCutIsomorphismDerivativeTransposeEquiv k F hφ hψ (Q.target b) (Q.source b)
      (Finsupp.single (⟨b, rfl, rfl, hb⟩ :
        Q.FoundationRelationArrow (Q.target b) (Q.source b)) 1) a := by
  let A : {a : Q.Arrow // Q.cut a = true} := ⟨a.val, a.property.2.2⟩
  let B : Q.FoundationRelationArrow (Q.target a.val) (Q.source a.val) :=
    ⟨b, a.property.1.symm, a.property.2.1.symm, hb⟩
  have hc := congrArg (fun c => c B)
    (Q.zeroCutIsomorphismDerivativeCoordinateEquiv_constantProjection k F hφ hψ A)
  have ht := Q.zeroCutIsomorphismDerivativeTransposeEquiv_single_apply k F hφ hψ
    (Q.target a.val) (Q.source a.val) B ⟨a.val, rfl, rfl, a.property.2.2⟩
  have h := (ht.trans hc).symm
  exact h.trans (Q.zeroCutIsomorphismDerivativeTransposeEquiv_coeff_transport k F hφ hψ
    a.property.2.1 a.property.1 B ⟨a.val, rfl, rfl, a.property.2.2⟩)

end ASGinzburg.CutQuiver
