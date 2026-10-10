import ASGinzburg.PathAutomorphismGradings
import ASGinzburg.FiniteComponentAutomorphismProducts
import ASGinzburg.BetweenSheetLinearEquiv
import ASGinzburg.ZAlgebraIsomorphisms

/-! A genuine vertex- and cut-preserving path algebra automorphism induces
an actual vertex-fixed isomorphism of the free unrolled path Z-algebra.
Neither linearity on arrows nor a period choice is imposed. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def VertexCutPathAutomorphism.cutComponentLinearEquiv
    (E : Q.VertexCutPathAutomorphism k) (i j : Q.Vertex) (c : ℤ) :
    Q.pathCutComponent k i j c ≃ₗ[k] Q.pathCutComponent k i j c where
  toFun f := ⟨VertexCutPathAutomorphism.componentLinearEquiv Q k E i j f.val,
    (VertexCutPathAutomorphism.component_preserves_cut Q k E i j c f.val).mp f.property⟩
  invFun f := ⟨(VertexCutPathAutomorphism.componentLinearEquiv Q k E i j).symm f.val,
    (VertexCutPathAutomorphism.component_preserves_cut Q k E i j c _).mpr
      (by simpa only [LinearEquiv.apply_symm_apply] using f.property)⟩
  left_inv f := Subtype.ext (LinearEquiv.symm_apply_apply _ f.val)
  right_inv f := Subtype.ext (LinearEquiv.apply_symm_apply _ f.val)
  map_add' f g := Subtype.ext (map_add _ f.val g.val)
  map_smul' a f := Subtype.ext (map_smul _ a f.val)

noncomputable def VertexCutPathAutomorphism.unrolledComponentLinearEquiv
    (E : Q.VertexCutPathAutomorphism k) (u v : Q.LiftVertex) :
    Q.UnrolledPathComponent k u v ≃ₗ[k] Q.UnrolledPathComponent k u v :=
  (Q.betweenSheetLinearEquiv k u v).symm.trans
    ((VertexCutPathAutomorphism.cutComponentLinearEquiv Q k E u.1 v.1 (v.2-u.2)).trans
      (Q.betweenSheetLinearEquiv k u v))

theorem VertexCutPathAutomorphism.unrolledComponentLinearEquiv_erase
    (E : Q.VertexCutPathAutomorphism k) (u v : Q.LiftVertex)
    (f : Q.UnrolledPathComponent k u v) :
    Q.unrolledPathEraseLinearMap k u v
      (VertexCutPathAutomorphism.unrolledComponentLinearEquiv Q k E u v f) =
      VertexCutPathAutomorphism.componentLinearEquiv Q k E u.1 v.1
        (Q.unrolledPathEraseLinearMap k u v f) := by
  unfold VertexCutPathAutomorphism.unrolledComponentLinearEquiv
  rw [LinearEquiv.trans_apply,LinearEquiv.trans_apply,Q.betweenSheetLinearEquiv_erase]
  change VertexCutPathAutomorphism.componentLinearEquiv Q k E u.1 v.1
    ((Q.betweenSheetLinearEquiv k u v).symm f).val = _
  rw [Q.betweenSheetLinearEquiv_symm_coe]

theorem unrolledPathEraseLinearMap_id (v : Q.LiftVertex) :
    Q.unrolledPathEraseLinearMap k v v (Q.unrolledPathId k v) = Q.pathId k v.1 := by
  simp [unrolledPathId,Q.unrolledPathEraseLinearMap_single,pathId,UnrolledPath.erase]

theorem VertexCutPathAutomorphism.unrolledComponentLinearEquiv_id
    (E : Q.VertexCutPathAutomorphism k) (v : Q.LiftVertex) :
    VertexCutPathAutomorphism.unrolledComponentLinearEquiv Q k E v v
      (Q.unrolledPathId k v) = Q.unrolledPathId k v := by
  apply Q.unrolledPathEraseLinearMap_injective k v v
  rw [VertexCutPathAutomorphism.unrolledComponentLinearEquiv_erase,
    Q.unrolledPathEraseLinearMap_id]
  exact (Q.pathComponentAlgebra k).totalAlgEquivComponentLinearEquiv_id E.val
    (VertexCutPathAutomorphism.fixes_vertex Q k E) v.1

theorem VertexCutPathAutomorphism.unrolledComponentLinearEquiv_comp
    (E : Q.VertexCutPathAutomorphism k) {u v w : Q.LiftVertex}
    (f : Q.UnrolledPathComponent k u v) (g : Q.UnrolledPathComponent k v w) :
    VertexCutPathAutomorphism.unrolledComponentLinearEquiv Q k E u w
      (Q.unrolledPathComp k g f) =
      Q.unrolledPathComp k
        (VertexCutPathAutomorphism.unrolledComponentLinearEquiv Q k E v w g)
        (VertexCutPathAutomorphism.unrolledComponentLinearEquiv Q k E u v f) := by
  apply Q.unrolledPathEraseLinearMap_injective k u w
  rw [VertexCutPathAutomorphism.unrolledComponentLinearEquiv_erase,
    Q.unrolledPathEraseLinearMap_comp,Q.unrolledPathEraseLinearMap_comp,
    VertexCutPathAutomorphism.unrolledComponentLinearEquiv_erase,
    VertexCutPathAutomorphism.unrolledComponentLinearEquiv_erase]
  exact (Q.pathComponentAlgebra k).totalAlgEquivComponentLinearEquiv_comp E.val
    (VertexCutPathAutomorphism.fixes_vertex Q k E) _ _

noncomputable def VertexCutPathAutomorphism.unrolledPathZAlgebraIsomorphism
    (E : Q.VertexCutPathAutomorphism k) :
    ZAlgebra.Isomorphism (Q.unrolledPathZAlgebra k) (Q.unrolledPathZAlgebra k) where
  map i j := VertexCutPathAutomorphism.unrolledComponentLinearEquiv Q k E
    (Q.heightEquiv.symm i) (Q.heightEquiv.symm j)
  map_id i := VertexCutPathAutomorphism.unrolledComponentLinearEquiv_id Q k E
    (Q.heightEquiv.symm i)
  map_comp f g := VertexCutPathAutomorphism.unrolledComponentLinearEquiv_comp Q k E f g

end ASGinzburg.CutQuiver
