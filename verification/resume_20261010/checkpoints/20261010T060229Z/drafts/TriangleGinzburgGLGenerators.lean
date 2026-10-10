import work.ASGinzburgDraft.TriangleArrowContragredient
import ASGinzburg.TriangleGLPathAutomorphism
import ASGinzburg.GinzburgGeneratorDifferentials
import work.ASGinzburgDraft.GinzburgArrowSubstitution

/-! Actual original and dual Ginzburg generator coordinates and the
contragredient extension of each triangle arrow GL change, with fixed loops. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

def triangleEdgeDualGinzburgPath (s i : Fin 3) :
    triangle333.GinzburgPath (triangleEdgeTarget s) s :=
  (triangle333.dualGinzburgArrowPath (triangleEdgeArrow s i)).transport triangle333
    (by apply Fin.ext; dsimp [triangle333,triangleEdgeArrow,triangleEdgeTarget]; omega)
    (by apply Fin.ext; dsimp [triangle333,triangleEdgeArrow]; omega)

noncomputable def triangleGinzburgOriginalCoordinates (s : Fin 3) :
    ArrowSpace333 k →ₗ[k] triangle333.GinzburgPathComponent k s (triangleEdgeTarget s) :=
  (triangle333.originalGinzburgLinearMap k s (triangleEdgeTarget s)).comp
    ((triangleArrowComponent k s (triangleEdgeTarget s)).subtype.comp
      (triangleEdgeArrowEquiv k s).toLinearMap)

theorem triangleGinzburgOriginalCoordinates_single (s i : Fin 3) (c : k) :
    triangleGinzburgOriginalCoordinates k s (Pi.single i c) =
      Finsupp.single ((triangleEdgePath s i).originalGinzburg triangle333) c := by
  simp only [triangleGinzburgOriginalCoordinates,LinearMap.comp_apply,
    LinearEquiv.coe_coe,Submodule.coe_subtype,triangleEdgeArrowEquiv_single,
    CutQuiver.originalGinzburgLinearMap_single]

noncomputable def triangleGinzburgDualCoordinates (s : Fin 3) :
    ArrowSpace333 k →ₗ[k] triangle333.GinzburgPathComponent k (triangleEdgeTarget s) s :=
  (Pi.basisFun k (Fin 3)).constr k
    (fun i => Finsupp.single (triangleEdgeDualGinzburgPath s i) (1 : k))

theorem triangleGinzburgDualCoordinates_single (s i : Fin 3) :
    triangleGinzburgDualCoordinates k s (Pi.single i 1) =
      Finsupp.single (triangleEdgeDualGinzburgPath s i) (1 : k) := by
  simpa only [triangleGinzburgDualCoordinates,Pi.basisFun_apply] using
    (Pi.basisFun k (Fin 3)).constr_basis k
      (fun j => Finsupp.single (triangleEdgeDualGinzburgPath s j) (1 : k)) i

theorem triangleGinzburgDualCoordinates_apply (s : Fin 3) (x : ArrowSpace333 k) :
    triangleGinzburgDualCoordinates k s x =
      ∑ i : Fin 3, x i • Finsupp.single (triangleEdgeDualGinzburgPath s i) (1 : k) := by
  simpa only [triangleGinzburgDualCoordinates,Pi.basisFun_repr] using
    (Pi.basisFun k (Fin 3)).constr_apply_fintype k
      (fun j => Finsupp.single (triangleEdgeDualGinzburgPath s j) (1 : k)) x

theorem triangleGinzburgDualCoordinates_mem_cohomological (s : Fin 3)
    (x : ArrowSpace333 k) :
    triangleGinzburgDualCoordinates k s x ∈
      triangle333.ginzburgCohomologicalComponent k (triangleEdgeTarget s) s (-1) := by
  rw [triangleGinzburgDualCoordinates_apply]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Finsupp.single_mem_supported
  simp [triangleEdgeDualGinzburgPath,CutQuiver.GinzburgPath.cohomologicalDegree_transport,
    CutQuiver.dualGinzburgArrowPath,CutQuiver.GinzburgPath.cohomologicalDegree,
    CutQuiver.GinzburgArrow.cohomologicalDegree]

noncomputable def triangleGinzburgGLArrowReplacement (g : TriangleGL333 k) :
    triangle333.GinzburgArrowReplacement k
  | .original a => triangle333.originalGinzburgLinearMap k _ _ (triangleGLArrowReplacement k g a)
  | .dual a => triangleGinzburgDualCoordinates k (triangle333.source a)
      (triangleArrowContragredient k (triangleGLArrowMatrix k g (triangle333.source a))
        (Pi.single (triangleGLArrowIndex a) 1))
  | .loop v => Finsupp.single (triangle333.ginzburgArrowPath (.loop v)) 1

theorem triangleGinzburgGLArrowReplacement_mem_cohomological (g : TriangleGL333 k)
    (a : triangle333.GinzburgArrow) :
    triangleGinzburgGLArrowReplacement k g a ∈
      triangle333.ginzburgCohomologicalComponent k (a.source triangle333) (a.target triangle333)
        (a.cohomologicalDegree triangle333) := by
  cases a with
  | original a =>
    change triangle333.originalGinzburgLinearMap k _ _ (triangleGLArrowReplacement k g a) ∈
      triangle333.ginzburgCohomologicalComponent k _ _ 0
    rw [←triangle333.originalGinzburgLinearMap_range k]
    exact LinearMap.mem_range_self _ _
  | dual a => exact triangleGinzburgDualCoordinates_mem_cohomological k _ _
  | loop v =>
    apply Finsupp.single_mem_supported
    rfl

end ASGinzburg
