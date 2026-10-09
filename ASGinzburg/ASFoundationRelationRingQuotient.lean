import ASGinzburg.ASFoundationRingPresentation
import ASGinzburg.FoundationBlockIdeals

/-! The original AS foundation ring is isomorphic to the actual
sheet-zero free-path ring modulo its genuine minimal relation ideal. -/
namespace ASGinzburg.ZAlgebra
universe u
variable {k : Type u} [Field k] (A : ZAlgebra.{u,u} k) (Q : CutQuiver)

theorem ASRegular.foundationRelationRingIdeal_eq_kernel (hAS : A.ASRegular Q) :
    (hAS.foundationRelationIdeal A Q).foundationIdeal Q=
      RingHom.ker (hAS.foundationRingPresentation A Q).toRingHom := by
  ext x
  change (∀ i j : Q.Vertex,x i j ∈ (hAS.foundationRelationIdeal A Q).hom
    (i.val : ℤ) (j.val : ℤ)) ↔ hAS.foundationRingPresentation A Q x=0
  exact (hAS.foundationRingPresentation_eq_zero_iff A Q x).symm

noncomputable abbrev ASRegular.FoundationRelationRing (hAS : A.ASRegular Q) :=
  (Q.unrolledPathZAlgebra k).FoundationAlgebra Q ⧸
    (hAS.foundationRelationIdeal A Q).foundationIdeal Q

noncomputable def ASRegular.foundationRelationRingAlgEquiv (hAS : A.ASRegular Q) :
    hAS.FoundationRelationRing A Q ≃ₐ[k] A.FoundationAlgebra Q :=
  (Ideal.quotientEquivAlgOfEq k (hAS.foundationRelationRingIdeal_eq_kernel A Q)).trans
    (hAS.foundationRingKernelQuotientEquiv A Q)

theorem ASRegular.foundationRelationRingAlgEquiv_apply_mk (hAS : A.ASRegular Q)
    (x : (Q.unrolledPathZAlgebra k).FoundationAlgebra Q) :
    hAS.foundationRelationRingAlgEquiv A Q
      (Ideal.Quotient.mk ((hAS.foundationRelationIdeal A Q).foundationIdeal Q) x)=
      hAS.foundationRingPresentation A Q x := by
  rw [ASRegular.foundationRelationRingAlgEquiv,AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk]
  rfl

end ASGinzburg.ZAlgebra
