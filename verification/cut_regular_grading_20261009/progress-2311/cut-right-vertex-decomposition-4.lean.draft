import ASGinzburg.PeriodCutRightVertexSpaces

/-! The regular ring is the actual finite product of its right vertex ideals. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cutRightVertexProjection (i : Q.Vertex) :
    E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)) →ₗ[k] E.cutRightVertexSpace Q i where
  toFun r := ⟨E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) i*r,by
    change _*(_*r)=_*r
    rw [← mul_assoc,E.cutVertexIdempotent_mul_self]⟩
  map_add' r s := Subtype.ext (mul_add _ r s)
  map_smul' c r := Subtype.ext (Algebra.mul_smul_comm c _ r)

theorem cutRightVertexProjection_value (i j : Q.Vertex) (r : E.cutRightVertexSpace Q j) :
    (E.cutRightVertexProjection Q i r.val).val=if i=j then r.val else 0 := by
  classical
  change E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) i*r.val=_
  by_cases h : i=j
  · subst j
    rw [if_pos rfl]
    exact r.property
  · rw [if_neg h,← r.property,← mul_assoc,E.cutVertexIdempotent_mul_ne _ i j h,zero_mul]

noncomputable def cutRightVertexDecompositionEquiv :
    E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)) ≃ₗ[k]
      (∀ i : Q.Vertex,E.cutRightVertexSpace Q i) where
  toFun r i := E.cutRightVertexProjection Q i r
  invFun f := ∑ i,(f i).val
  left_inv r := by
    change (∑ i,E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) i*r)=r
    rw [← Finset.sum_mul,E.sum_cutVertexIdempotent,one_mul]
  right_inv f := by
    classical
    funext i
    apply Subtype.ext
    change E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) i*(∑ j,(f j).val)=(f i).val
    rw [Finset.mul_sum]
    change (∑ j,(E.cutRightVertexProjection Q i (f j).val).val)=(f i).val
    simp [E.cutRightVertexProjection_value]
  map_add' r s := by funext i;exact (E.cutRightVertexProjection Q i).map_add r s
  map_smul' c r := by funext i;exact (E.cutRightVertexProjection Q i).map_smul c r

end ASGinzburg.ZAlgebra.PeriodIso
