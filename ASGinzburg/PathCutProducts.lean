import ASGinzburg.PathCutGrading
import ASGinzburg.GinzburgSupportedProducts

/-! Actual cut homogeneous ordinary path components multiply in the
sum of the degrees; their concrete projections act diagonally. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem pathCutComponent_comp {u v w : Q.Vertex} {c d : ℤ}
    {f : Q.PathComponent k u v} (hf : f ∈ Q.pathCutComponent k u v c)
    {g : Q.PathComponent k v w} (hg : g ∈ Q.pathCutComponent k v w d) :
    Q.pathComp k g f ∈ Q.pathCutComponent k u w (c+d) := by
  apply (Q.originalGinzburgLinearMap_cut_iff k (c+d) _).mp
  rw [Q.originalGinzburgLinearMap_comp]
  exact Q.ginzburgCutComponent_comp k (Q.originalGinzburgLinearMap_cut k hf)
    (Q.originalGinzburgLinearMap_cut k hg)

theorem pathCutProjection_on_cut {u v : Q.Vertex} (c d : ℤ)
    {f : Q.PathComponent k u v} (hf : f ∈ Q.pathCutComponent k u v d) :
    Q.pathCutProjection k u v c f=if d=c then f else 0 := by
  apply Q.originalGinzburgLinearMap_injective k u v
  rw [Q.originalGinzburgLinearMap_cutProjection,
    Q.ginzburgCutProjection_on_cut k c d (Q.originalGinzburgLinearMap_cut k hf)]
  by_cases h : d=c <;> simp [h]

end ASGinzburg.CutQuiver
