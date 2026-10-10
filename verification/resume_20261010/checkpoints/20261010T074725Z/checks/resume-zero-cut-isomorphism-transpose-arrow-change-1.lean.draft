import work.ASGinzburgDraft.FoundationCutArrowCoordinates
import work.ASGinzburgDraft.ZeroCutIsomorphismDerivativeBasisTransport
import work.ASGinzburgDraft.PathSubstitutionAutomorphismCriteria

/-! The genuine dual change of native derivative bases gives a genuine
linear path automorphism on the cut arrows, fixing all noncut arrows. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]
variable {φ ψ : Q.Potential k}
variable (F : ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ)
  (Q.unrolledJacobianZAlgebra k ψ))
variable (hφ : Q.GinzburgRegular k φ) (hψ : Q.GinzburgRegular k ψ)

noncomputable def zeroCutIsomorphismTransposeArrowLinearEquiv (i j : Q.Vertex) :
    Q.pathArrowComponent k i j ≃ₗ[k] Q.pathArrowComponent k i j :=
  if h : j.val < i.val then
    (Q.foundationCutArrowCoordinateEquiv k j i h).symm.trans
      ((Q.zeroCutIsomorphismDerivativeTransposeEquiv k F hφ hψ j i).trans
        (Q.foundationCutArrowCoordinateEquiv k j i h))
  else LinearEquiv.refl k _

theorem zeroCutIsomorphismTransposeArrowLinearEquiv_backward (i j : Q.Vertex)
    (hij : i.val < j.val) :
    Q.zeroCutIsomorphismTransposeArrowLinearEquiv k F hφ hψ j i =
      (Q.foundationCutArrowCoordinateEquiv k i j hij).symm.trans
        ((Q.zeroCutIsomorphismDerivativeTransposeEquiv k F hφ hψ i j).trans
          (Q.foundationCutArrowCoordinateEquiv k i j hij)) := by
  rw [zeroCutIsomorphismTransposeArrowLinearEquiv, dif_pos hij]

theorem zeroCutIsomorphismTransposeArrowLinearEquiv_forward (i j : Q.Vertex)
    (hij : i.val < j.val) :
    Q.zeroCutIsomorphismTransposeArrowLinearEquiv k F hφ hψ i j =
      LinearEquiv.refl k _ := by
  rw [zeroCutIsomorphismTransposeArrowLinearEquiv, dif_neg (by omega)]

noncomputable def zeroCutIsomorphismTransposeArrowAutomorphism :
    Q.VertexCutPathAutomorphism k :=
  Q.pathArrowLinearAutomorphism k
    (Q.zeroCutIsomorphismTransposeArrowLinearEquiv k F hφ hψ)

theorem zeroCutIsomorphismTransposeArrowAutomorphism_arrow (a : Q.Arrow) :
    VertexCutPathAutomorphism.arrowReplacement Q k
      (Q.zeroCutIsomorphismTransposeArrowAutomorphism k F hφ hψ) a =
    (Q.zeroCutIsomorphismTransposeArrowLinearEquiv k F hφ hψ
      (Q.source a) (Q.target a) (Q.pathArrowBasisElement k a)).val := by
  unfold VertexCutPathAutomorphism.arrowReplacement zeroCutIsomorphismTransposeArrowAutomorphism
  rw [VertexCutPathAutomorphism.component_of_substitution Q k _ _ (by rfl),
    pathIdentityArrowReplacement, Q.pathArrowSubstitution_arrow]
  rfl

theorem zeroCutIsomorphismTransposeArrowAutomorphism_cut_arrow (a : Q.Arrow)
    (ha : Q.cut a = true) :
    VertexCutPathAutomorphism.arrowReplacement Q k
      (Q.zeroCutIsomorphismTransposeArrowAutomorphism k F hφ hψ) a =
    (Q.foundationCutArrowCoordinateEquiv k (Q.target a) (Q.source a) (Q.backward a ha)
      (Q.zeroCutIsomorphismDerivativeTransposeEquiv k F hφ hψ (Q.target a) (Q.source a)
        (Finsupp.single (⟨a, rfl, rfl, ha⟩ : Q.FoundationRelationArrow (Q.target a) (Q.source a)) 1))).val := by
  let C := Q.foundationCutArrowCoordinateEquiv k (Q.target a) (Q.source a) (Q.backward a ha)
  let b : Q.FoundationRelationArrow (Q.target a) (Q.source a) := ⟨a, rfl, rfl, ha⟩
  have hb : C (Finsupp.single b 1) = Q.pathArrowBasisElement k a := by
    apply Subtype.ext
    exact Q.foundationCutArrowCoordinateEquiv_single k _ _ _ b 1
  rw [Q.zeroCutIsomorphismTransposeArrowAutomorphism_arrow,
    Q.zeroCutIsomorphismTransposeArrowLinearEquiv_backward k F hφ hψ _ _ (Q.backward a ha)]
  change (C.symm.trans ((Q.zeroCutIsomorphismDerivativeTransposeEquiv k F hφ hψ _ _).trans C)
    (Q.pathArrowBasisElement k a)).val = _
  rw [← hb, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

theorem zeroCutIsomorphismTransposeArrowAutomorphism_noncut_arrow (a : Q.Arrow)
    (ha : Q.cut a = false) :
    VertexCutPathAutomorphism.arrowReplacement Q k
      (Q.zeroCutIsomorphismTransposeArrowAutomorphism k F hφ hψ) a =
      Q.pathIdentityArrowReplacement k a := by
  rw [Q.zeroCutIsomorphismTransposeArrowAutomorphism_arrow,
    Q.zeroCutIsomorphismTransposeArrowLinearEquiv_forward k F hφ hψ _ _ (Q.forward a ha)]
  rfl

end ASGinzburg.CutQuiver
