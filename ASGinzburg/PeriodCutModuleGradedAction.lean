import ASGinzburg.PeriodCornerModuleGradeInclusions

/-! Actual homogeneous degree-m right multiplication raises module degree by m. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cutHomogeneousRightOperator_lof_mem_grade
    (M : (E.cornerCoverZAlgebra Q).RightModule) (m : ℕ)
    (r : E.CutGradedBlock (fun i : Q.Vertex => (i.val:ℤ)) m)
    (q : ℤ) (j : Q.Vertex) (v : E.CornerModuleSpace Q M (j,-q)) :
    E.cutHomogeneousRightOperator Q M m r
      (DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) (j,-q) v)∈
        E.cornerModuleGrade Q M (q+(m:ℤ)) := by
  rw [E.cutHomogeneousRightOperator_lof,E.cutRightColumnMap_apply]
  apply Submodule.sum_mem
  intro i hi
  apply E.cornerModule_lof_mem_grade
  dsimp [cutRightSource]
  ring

theorem cutHomogeneousRightOperator_degreeInsertion_mem
    (M : (E.cornerCoverZAlgebra Q).RightModule) (m : ℕ)
    (r : E.CutGradedBlock (fun i : Q.Vertex => (i.val:ℤ)) m)
    (q : ℤ) (v : E.CornerModuleDegreeSpace Q M q) :
    E.cutHomogeneousRightOperator Q M m r (E.cornerModuleDegreeInsertion Q M q v)∈
      E.cornerModuleGrade Q M (q+(m:ℤ)) := by
  refine DirectSum.induction_on v ?_ ?_ ?_
  · rw [map_zero,map_zero]
    exact Submodule.zero_mem _
  · intro j x
    change E.cutHomogeneousRightOperator Q M m r
      (E.cornerModuleDegreeInsertion Q M q
        (DirectSum.lof k Q.Vertex (fun i => E.CornerModuleSpace Q M (i,-q)) j x))∈_
    rw [E.cornerModuleDegreeInsertion_lof]
    exact E.cutHomogeneousRightOperator_lof_mem_grade Q M m r q j x
  · intro x y hx hy
    rw [map_add,map_add]
    exact Submodule.add_mem _ hx hy

theorem cutRightRingModule_smul_mem_grade
    (M : (E.cornerCoverZAlgebra Q).RightModule) (m : ℕ)
    (r : E.CutGradedBlock (fun i : Q.Vertex => (i.val:ℤ)) m)
    (q : ℤ) (v : E.CornerModuleTotalSpace Q M) (hv : v∈E.cornerModuleGrade Q M q) :
    (MulOpposite.op (E.cutHomogeneousInclusion (fun i : Q.Vertex => (i.val:ℤ)) m r)) • v∈
      E.cornerModuleGrade Q M (q+(m:ℤ)) := by
  rcases hv with ⟨x,rfl⟩
  rw [E.cutRightRingModule_homogeneous_smul]
  exact E.cutHomogeneousRightOperator_degreeInsertion_mem Q M m r q x

end ASGinzburg.ZAlgebra.PeriodIso
