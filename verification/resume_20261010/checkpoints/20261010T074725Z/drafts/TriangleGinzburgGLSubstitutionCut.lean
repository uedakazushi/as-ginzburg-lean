import work.ASGinzburgDraft.TriangleGinzburgGLSubstitutionInverse

/-! The actual extended triangle GL substitutions preserve cut degree
and restrict to actual fixed-cut cohomological component equivalences. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

theorem triangleGinzburgDualCoordinates_mem_cut (s : Fin 3) (x : ArrowSpace333 k) :
    triangleGinzburgDualCoordinates k s x ∈
      triangle333.ginzburgCutComponent k (triangleEdgeTarget s) s
        (1-(triangle333.cutDegree (triangleEdgeArrow s 0) : ℤ)) := by
  rw [triangleGinzburgDualCoordinates_apply]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Finsupp.single_mem_supported
  simp only [triangleEdgeDualGinzburgPath,CutQuiver.dualGinzburgArrowPath]
  fin_cases s <;> fin_cases i <;> rfl

theorem triangleGinzburgGLArrowReplacement_mem_cut (g : TriangleGL333 k)
    (a : triangle333.GinzburgArrow) :
    triangleGinzburgGLArrowReplacement k g a ∈
      triangle333.ginzburgCutComponent k (a.source triangle333) (a.target triangle333)
        (a.cutDegree triangle333) := by
  cases a with
  | original a =>
    exact triangle333.originalGinzburgLinearMap_cut k (triangleGLArrowReplacement_mem_cut k g a)
  | dual a =>
    have hd := triangleGinzburgDualCoordinates_mem_cut k (triangle333.source a)
      (triangleArrowContragredient k (triangleGLArrowMatrix k g (triangle333.source a))
        (Pi.single (triangleGLArrowIndex a) 1))
    fin_cases a <;> exact hd
  | loop v =>
    apply Finsupp.single_mem_supported
    rfl

noncomputable def triangleGinzburgGLCutCohomologicalEquiv (g : TriangleGL333 k)
    (i j : triangle333.Vertex) (q c : ℤ) :
    triangle333.ginzburgCutCohomologicalComponent k i j q c ≃ₗ[k]
      triangle333.ginzburgCutCohomologicalComponent k i j q c :=
  triangle333.ginzburgArrowSubstitutionCutCohomologicalEquiv k
    (triangleGinzburgGLArrowReplacement k g) (triangleGinzburgGLArrowReplacement k (g⁻¹))
    (triangleGinzburgGLArrowReplacement_inverse k g)
    (by intro a; simpa only [inv_inv] using triangleGinzburgGLArrowReplacement_inverse k (g⁻¹) a)
    (triangleGinzburgGLArrowReplacement_mem_cohomological k g)
    (triangleGinzburgGLArrowReplacement_mem_cohomological k (g⁻¹))
    (triangleGinzburgGLArrowReplacement_mem_cut k g)
    (triangleGinzburgGLArrowReplacement_mem_cut k (g⁻¹)) i j q c

@[simp] theorem triangleGinzburgGLCutCohomologicalEquiv_coe (g : TriangleGL333 k)
    (i j : triangle333.Vertex) (q c : ℤ)
    (f : triangle333.ginzburgCutCohomologicalComponent k i j q c) :
    (triangleGinzburgGLCutCohomologicalEquiv k g i j q c f).val =
      triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g)
        i j f.val := rfl

end ASGinzburg
