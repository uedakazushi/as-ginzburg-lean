import ASGinzburg.GinzburgCutProjections

/-! Every actual finite path polynomial is the finite sum of its
homogeneous cut projections, indexed by the degrees in its support. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgCutProjection_apply {u v : Q.Vertex} (c : ℤ)
    (f : Q.GinzburgPathComponent k u v) (p : Q.GinzburgPath u v) :
    Q.ginzburgCutProjection k u v c f p=if p.cutDegree=c then f p else 0 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    by_cases h : p.cutDegree=c <;> simp [map_add,hf,hg,h]
  | single q a =>
    rw [ginzburgCutProjection_single]
    by_cases h : q=p
    · subst q
      by_cases h : p.cutDegree=c <;> simp [h]
    · by_cases hq : q.cutDegree=c <;> by_cases hp : p.cutDegree=c <;>
        simp [hq,hp,Ne.symm h]

noncomputable def ginzburgCutSupport {u v : Q.Vertex} (f : Q.GinzburgPathComponent k u v) :
    Finset ℤ := by
  classical
  exact f.support.image GinzburgPath.cutDegree

theorem ginzburgCutProjection_sum {u v : Q.Vertex} (f : Q.GinzburgPathComponent k u v) :
    ∑ c ∈ Q.ginzburgCutSupport k f, Q.ginzburgCutProjection k u v c f=f := by
  classical
  ext p
  simp only [Finsupp.finset_sum_apply,ginzburgCutProjection_apply]
  by_cases hp : p ∈ f.support
  · have hc : p.cutDegree ∈ Q.ginzburgCutSupport k f := Finset.mem_image.mpr ⟨p,hp,rfl⟩
    simp [eq_comm,hc]
  · have hf : f p=0 := Finsupp.notMem_support_iff.mp hp
    simp [hf]

end ASGinzburg.CutQuiver
