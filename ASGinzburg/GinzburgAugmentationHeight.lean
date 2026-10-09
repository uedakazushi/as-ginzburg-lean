import ASGinzburg.GinzburgAugmentationRegularity

/-! Genuine nonempty paths have positive height difference. Accordingly,
the augmentation component is the whole component below its endpoint,
and zero elsewhere, exactly as for the representable radical. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

theorem GinzburgPath.length_pos_of_winding_pos {u v : Q.Vertex}
    (p : Q.GinzburgPath u v) (hw : 0<p.winding) : 0<p.length := by
  cases p with
  | nil => simp [GinzburgPath.winding] at hw
  | snoc p a ha => simp [GinzburgPath.length]

theorem GinzburgPath.winding_eq_lift_height_difference {x y : Q.LiftVertex}
    (p : Q.GinzburgPath x.1 y.1) (hc : p.cutDegree=y.2-x.2) :
    p.winding=Q.height y-Q.height x := by
  rw [p.winding_formula,hc]
  unfold height
  ring

universe u
variable (k : Type u) [Field k]

theorem ginzburgAugmentationAtDegree_eq_cut_of_height_lt (x y : Q.LiftVertex)
    (q : ℤ) (hxy : Q.height x<Q.height y) :
    Q.ginzburgAugmentationAtDegree k x.1 y.1 q (y.2-x.2)=
      Q.ginzburgCutCohomologicalComponent k x.1 y.1 q (y.2-x.2) := by
  rw [Q.ginzburgAugmentationAtDegree_eq_inf]
  apply inf_eq_right.mpr
  intro f hf
  change f ∈ Finsupp.supported k k {p : Q.GinzburgPath x.1 y.1 | 0<p.length}
  rw [Finsupp.mem_supported]
  intro p hp
  have hfc : f ∈ Finsupp.supported k k
      {p : Q.GinzburgPath x.1 y.1 | p.cutDegree=y.2-x.2} := hf.2
  have hc := (Finsupp.mem_supported k f).mp hfc hp
  have hw : 0<p.winding := by
    rw [p.winding_eq_lift_height_difference Q hc]
    omega
  exact p.length_pos_of_winding_pos Q hw

theorem ginzburgAugmentationAtDegree_eq_bot_of_not_height_lt (x y : Q.LiftVertex)
    (q : ℤ) (hxy : ¬Q.height x<Q.height y) :
    Q.ginzburgAugmentationAtDegree k x.1 y.1 q (y.2-x.2)=⊥ := by
  apply bot_unique
  intro f hf
  rw [Submodule.mem_bot]
  apply Finsupp.ext
  intro p
  by_contra hp
  simp only [Finsupp.zero_apply] at hp
  change f ∈ Finsupp.supported k k
    {p : Q.GinzburgPath x.1 y.1 | 0<p.length ∧ p.cohomologicalDegree=q ∧ p.cutDegree=y.2-x.2} at hf
  have hpc := (Finsupp.mem_supported k f).mp hf (Finsupp.mem_support_iff.mpr hp)
  have hw := p.winding_pos_of_length_pos hpc.1
  rw [p.winding_eq_lift_height_difference Q hpc.2.2] at hw
  exact hxy (by omega)

end ASGinzburg.CutQuiver
