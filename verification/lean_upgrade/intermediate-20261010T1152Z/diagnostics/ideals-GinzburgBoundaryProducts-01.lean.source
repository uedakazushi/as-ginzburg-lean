import ASGinzburg.GinzburgBoundarySpaces

/-! The genuine degree zero boundary spaces are closed under multiplication
on both sides by ordinary paths and their finite linear combinations. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem originalGinzburgLinearMap_degreeZero {u v : Q.Vertex} (f : Q.PathComponent k u v) :
    Q.originalGinzburgLinearMap k u v f ∈ Q.ginzburgCohomologicalComponent k u v 0 := by
  rw [←Q.originalGinzburgLinearMap_range k]
  exact LinearMap.mem_range_self _ _

theorem ginzburgBoundarySpace_comp_left (φ : Q.Potential k) {u v w : Q.Vertex}
    {f : Q.PathComponent k u v} (hf : f ∈ Q.ginzburgBoundarySpace k φ u v)
    (g : Q.PathComponent k v w) : Q.pathComp k g f ∈ Q.ginzburgBoundarySpace k φ u w := by
  obtain ⟨x,hx⟩ := (Q.ginzburgBoundarySpace_mem_iff k φ u v f).mp hf
  have hg := Q.originalGinzburgLinearMap_degreeZero k g
  have hy : Q.ginzburgPathComp k (Q.originalGinzburgLinearMap k v w g) x.val ∈
      Q.ginzburgCohomologicalComponent k u w (-1) := by
    simpa only [add_zero] using Q.ginzburgCohomologicalComponent_comp k x.property hg
  apply (Q.ginzburgBoundarySpace_mem_iff k φ u w _).mpr
  refine ⟨⟨_,hy⟩,?_⟩
  change Q.ginzburgDifferential k φ u w
    (Q.ginzburgPathComp k (Q.originalGinzburgLinearMap k v w g) x.val)=_
  rw [Q.ginzburgDifferential_comp,Q.ginzburgDifferential_original,
    Q.ginzburgSignMap_homogeneous k hg,ginzburgSign_zero,one_smul,hx,
    Q.originalGinzburgLinearMap_comp]
  simp

theorem ginzburgBoundarySpace_comp_right (φ : Q.Potential k) {u v w : Q.Vertex}
    {g : Q.PathComponent k v w} (hg : g ∈ Q.ginzburgBoundarySpace k φ v w)
    (f : Q.PathComponent k u v) : Q.pathComp k g f ∈ Q.ginzburgBoundarySpace k φ u w := by
  obtain ⟨x,hx⟩ := (Q.ginzburgBoundarySpace_mem_iff k φ v w g).mp hg
  have hf := Q.originalGinzburgLinearMap_degreeZero k f
  have hy : Q.ginzburgPathComp k x.val (Q.originalGinzburgLinearMap k u v f) ∈
      Q.ginzburgCohomologicalComponent k u w (-1) := by
    simpa only [zero_add] using Q.ginzburgCohomologicalComponent_comp k hf x.property
  apply (Q.ginzburgBoundarySpace_mem_iff k φ u w _).mpr
  refine ⟨⟨_,hy⟩,?_⟩
  change Q.ginzburgDifferential k φ u w
    (Q.ginzburgPathComp k x.val (Q.originalGinzburgLinearMap k u v f))=_
  rw [Q.ginzburgDifferential_comp,Q.ginzburgDifferential_original,hx,
    Q.originalGinzburgLinearMap_comp]
  simp

end ASGinzburg.CutQuiver
