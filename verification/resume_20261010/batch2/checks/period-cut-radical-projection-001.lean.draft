import ASGinzburg.PeriodCutPositiveActionRadical

/-! Every component of the actual graded radical product lies in the
cover's positive-action submodule. Together with the inclusion of positive
actions, this identifies the native ring radical action componentwise. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

theorem cornerCoverHom_diagonal_eq_zero_of_mem_radical (x : Q.LiftVertex)
    (a : E.CornerCoverHom Q x x) (ha : a.val ∈ E.cutGradedJacobson Q) : a = 0 := by
  have hp := a.property
  change a.val ∈ E.integerCorner Q (x.2 - x.2) x.1 x.1 at hp
  rw [sub_self, show (0 : ℤ) = (0 : ℕ) from rfl, E.integerCorner_ofNat] at hp
  obtain ⟨f, hf⟩ := hp
  have hd := (E.mem_cutGradedJacobson_iff Q a.val).mp ha x.1
  rw [← hf, E.cutHomogeneousComponentLinear_apply] at hd
  change (DirectSum.of (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ))) 0
    (E.cutMatrixComponent (fun i : Q.Vertex => (i.val : ℤ)) 0 x.1 x.1 f)) 0 x.1 x.1 = 0 at hd
  rw [DirectSum.of_eq_same, E.cutMatrixComponent_apply_same] at hd
  apply Subtype.ext
  rw [← hf, hd, map_zero]

theorem cornerModuleMap_mem_positiveActionSpan_of_radical
    (M : (E.cornerCoverZAlgebra Q).RightModule) {x y : Q.LiftVertex}
    (a : E.CornerCoverHom Q x y) (ha : a.val ∈ E.cutGradedJacobson Q)
    (w : E.CornerModuleSpace Q M y) :
    E.cornerModuleMap Q M x y a w ∈
      (E.cornerCoverZAlgebra Q).positiveActionSpan M (Q.heightEquiv x) := by
  by_cases hxy : Q.heightEquiv x < Q.heightEquiv y
  · exact Submodule.subset_span ⟨Q.heightEquiv y, hxy, w,
      E.cornerCoordinateHomEquiv Q x y a, rfl⟩
  · by_cases he : x = y
    · subst y
      rw [E.cornerCoverHom_diagonal_eq_zero_of_mem_radical Q x a ha,
        map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
    · have hgt : Q.heightEquiv y < Q.heightEquiv x := by
        have hn : Q.heightEquiv x ≠ Q.heightEquiv y := fun h => he (Q.heightEquiv.injective h)
        exact lt_of_le_of_ne (le_of_not_gt hxy) (Ne.symm hn)
      have hz : a = 0 := by
        apply (E.cornerCoordinateHomEquiv Q x y).injective
        rw [map_zero]
        exact (E.cornerCoverZAlgebra Q).positive hgt _
      rw [hz, map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _

theorem cornerPositiveActionSpan_component_lof_mem
    (M : (E.cornerCoverZAlgebra Q).RightModule) (x y : Q.LiftVertex)
    (w : E.CornerModuleSpace Q M y)
    (hw : w ∈ (E.cornerCoverZAlgebra Q).positiveActionSpan M (Q.heightEquiv y)) :
    DirectSum.component k Q.LiftVertex (E.CornerModuleSpace Q M) x
        (DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) y w) ∈
      (E.cornerCoverZAlgebra Q).positiveActionSpan M (Q.heightEquiv x) := by
  classical
  by_cases h : y = x
  · subst y
    rw [DirectSum.component.lof_self]
    exact hw
  · rw [DirectSum.component.of, dif_neg h]
    exact Submodule.zero_mem _

theorem cutHomogeneousRadicalAction_component_lof_mem
    (M : (E.cornerCoverZAlgebra Q).RightModule) (m : ℕ)
    (r : E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) m)
    (hr : E.cutHomogeneousInclusion (fun i : Q.Vertex => (i.val : ℤ)) m r ∈
      E.cutGradedJacobson Q) (y : Q.LiftVertex) (w : E.CornerModuleSpace Q M y)
    (x : Q.LiftVertex) :
    DirectSum.component k Q.LiftVertex (E.CornerModuleSpace Q M) x
        (E.cutHomogeneousRightOperator Q M m r
          (DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) y w)) ∈
      (E.cornerCoverZAlgebra Q).positiveActionSpan M (Q.heightEquiv x) := by
  classical
  rw [E.cutHomogeneousRightOperator_lof, E.cutRightColumnMap_apply, map_sum]
  apply Submodule.sum_mem
  intro i hi
  let a := E.cutCornerEntry Q m (cutRightSource Q m y i) y
    (cutRightSource_difference Q m y i) (r i y.1)
  have ha : a.val ∈ E.cutGradedJacobson Q := by
    change E.cutHomogeneousComponentLinear (fun j : Q.Vertex => (j.val : ℤ)) m i y.1
      (r i y.1) ∈ E.cutGradedJacobson Q
    rw [← E.cutHomogeneous_corner_projection (fun j : Q.Vertex => (j.val : ℤ)) m i y.1 r]
    exact (E.cutGradedJacobson Q).mul_mem_right
      (E.cutVertexIdempotent (fun j : Q.Vertex => (j.val : ℤ)) i)
      ((E.cutGradedJacobson Q).mul_mem_left
        (E.cutVertexIdempotent (fun j : Q.Vertex => (j.val : ℤ)) y.1) hr)
  exact E.cornerPositiveActionSpan_component_lof_mem Q M x (cutRightSource Q m y i)
    (E.cornerModuleMap Q M (cutRightSource Q m y i) y a w)
    (E.cornerModuleMap_mem_positiveActionSpan_of_radical Q M a ha w)

theorem cutRightRepresentation_radical_component_mem
    (M : (E.cornerCoverZAlgebra Q).RightModule)
    (r : E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))
    (hr : r ∈ E.cutGradedJacobson Q) (w : E.CornerModuleTotalSpace Q M)
    (x : Q.LiftVertex) :
    DirectSum.component k Q.LiftVertex (E.CornerModuleSpace Q M) x
        ((E.cutRightRepresentation Q M r).unop w) ∈
      (E.cornerCoverZAlgebra Q).positiveActionSpan M (Q.heightEquiv x) := by
  classical
  refine DirectSum.induction_on w ?_ ?_ ?_
  · rw [map_zero, map_zero]
    exact Submodule.zero_mem _
  · intro y v
    change DirectSum.component k Q.LiftVertex (E.CornerModuleSpace Q M) x
      ((E.cutRightRepresentation Q M r).unop
        (DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) y v)) ∈ _
    rw [← DirectSum.sum_support_of r]
    simp only [map_sum, Finset.unop_sum, LinearMap.sum_apply]
    apply Submodule.sum_mem
    intro m hm
    have hmrad := E.cutGradedJacobson_homogeneous Q r hr m
    rw [E.cutHomogeneousProjection_apply] at hmrad
    change DirectSum.component k Q.LiftVertex (E.CornerModuleSpace Q M) x
      ((E.cutRightRepresentation Q M
        (E.cutHomogeneousInclusion (fun i : Q.Vertex => (i.val : ℤ)) m (r m))).unop
        (DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) y v)) ∈ _
    rw [E.cutRightRepresentation_homogeneous]
    exact E.cutHomogeneousRadicalAction_component_lof_mem Q M m (r m) hmrad y v x
  · intro a b ha hb
    rw [map_add, map_add]
    exact Submodule.add_mem _ ha hb

theorem cornerRadicalActionSpan_component_mem
    (M : (E.cornerCoverZAlgebra Q).RightModule) (w : E.CornerModuleTotalSpace Q M)
    (hw : w ∈ (E.cornerGradedRightModule Q M).gradedRadicalActionSpan) (x : Q.LiftVertex) :
    DirectSum.component k Q.LiftVertex (E.CornerModuleSpace Q M) x w ∈
      (E.cornerCoverZAlgebra Q).positiveActionSpan M (Q.heightEquiv x) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨r, hr, v, rfl⟩ := hw
    exact E.cutRightRepresentation_radical_component_mem Q M r hr v x
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add a b ha hb iha ihb =>
    rw [map_add]
    exact Submodule.add_mem _ iha ihb
  | smul c a ha ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ih

end ASGinzburg.ZAlgebra.PeriodIso
