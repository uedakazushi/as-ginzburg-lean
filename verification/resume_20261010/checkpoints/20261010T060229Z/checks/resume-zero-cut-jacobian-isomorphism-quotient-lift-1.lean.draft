import work.ASGinzburgDraft.ZeroCutJacobianFoundationComparison

/-! The genuine free noncut lift induces exactly the given foundation
isomorphism on the native quotient by cut-arrow derivatives. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]
variable {φ ψ : Q.Potential k}
variable (F : ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ)
  (Q.unrolledJacobianZAlgebra k ψ))

theorem zeroCutIsomorphismFreePathAlgEquiv_jacobian_mem_iff (x : Q.ZeroCutPathRing k) :
    Q.zeroCutIsomorphismFreePathAlgEquiv k F x ∈ Q.zeroCutJacobianIdeal k ψ ↔
      x ∈ Q.zeroCutJacobianIdeal k φ := by
  rw [Q.zeroCutJacobianIdeal_eq_foundationKernel,Q.zeroCutJacobianIdeal_eq_foundationKernel]
  change Q.zeroCutJacobianFoundationAlgHom k ψ (Q.zeroCutIsomorphismFreePathAlgEquiv k F x) = 0 ↔
    Q.zeroCutJacobianFoundationAlgHom k φ x = 0
  rw [Q.zeroCutIsomorphismFreePathAlgEquiv_intertwines]
  exact (F.foundationAlgEquiv Q).map_eq_zero_iff

noncomputable def zeroCutJacobianIsomorphismQuotientLift :
    Q.ZeroCutJacobianRing k φ ≃ₐ[k] Q.ZeroCutJacobianRing k ψ :=
  (Q.zeroCutJacobianFoundationAlgEquiv k φ).trans
    ((F.foundationAlgEquiv Q).trans (Q.zeroCutJacobianFoundationAlgEquiv k ψ).symm)

theorem zeroCutJacobianIsomorphismQuotientLift_apply_mk (x : Q.ZeroCutPathRing k) :
    Q.zeroCutJacobianIsomorphismQuotientLift k F
      (Ideal.Quotient.mk (Q.zeroCutJacobianIdeal k φ) x) =
        Ideal.Quotient.mk (Q.zeroCutJacobianIdeal k ψ) (Q.zeroCutIsomorphismFreePathAlgEquiv k F x) := by
  apply (Q.zeroCutJacobianFoundationAlgEquiv k ψ).injective
  change Q.zeroCutJacobianFoundationAlgEquiv k ψ
    ((Q.zeroCutJacobianFoundationAlgEquiv k ψ).symm
      (F.foundationAlgEquiv Q (Q.zeroCutJacobianFoundationAlgEquiv k φ
        (Ideal.Quotient.mk (Q.zeroCutJacobianIdeal k φ) x)))) = _
  rw [AlgEquiv.apply_symm_apply,Q.zeroCutJacobianFoundationAlgEquiv_apply_mk,
    Q.zeroCutJacobianFoundationAlgEquiv_apply_mk]
  exact (Q.zeroCutIsomorphismFreePathAlgEquiv_intertwines k F x).symm

end ASGinzburg.CutQuiver
