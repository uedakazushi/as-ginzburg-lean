import ASGinzburg.GinzburgPathDifferential
import ASGinzburg.GinzburgSupportedProducts

/-! Degree and cut preservation of the signed path differential. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem GinzburgPath.differential_degree (φ : Q.Potential k) {u v : Q.Vertex}
    (p : Q.GinzburgPath u v) :
    p.differential Q k φ ∈ Q.ginzburgCohomologicalComponent k u v (p.cohomologicalDegree+1) := by
  induction p with
  | nil => simp
  | snoc p a h ih =>
    subst h
    rw [differential]
    apply Submodule.add_mem
    · have hp : Finsupp.single p (1:k) ∈
          Q.ginzburgCohomologicalComponent k _ _ p.cohomologicalDegree :=
        Finsupp.single_mem_supported _ _ rfl
      simpa only [cohomologicalDegree,add_assoc] using
        Q.ginzburgCohomologicalComponent_comp k hp (Q.ginzburgGeneratorDifferential_degree k φ a)
    · apply Submodule.smul_mem
      have ha : Finsupp.single (Q.ginzburgArrowPath a) (1:k) ∈
          Q.ginzburgCohomologicalComponent k _ _ (a.cohomologicalDegree Q) := by
        apply Finsupp.single_mem_supported
        simp [ginzburgArrowPath,cohomologicalDegree]
      convert Q.ginzburgCohomologicalComponent_comp k ih ha using 1
      simp [cohomologicalDegree,add_comm,add_left_comm]

theorem GinzburgPath.differential_cut (φ : Q.Potential k) {u v : Q.Vertex}
    (p : Q.GinzburgPath u v) :
    p.differential Q k φ ∈ Q.ginzburgCutComponent k u v p.cutDegree := by
  induction p with
  | nil => simp
  | snoc p a h ih =>
    subst h
    rw [differential]
    apply Submodule.add_mem
    · have hp : Finsupp.single p (1:k) ∈ Q.ginzburgCutComponent k _ _ p.cutDegree :=
        Finsupp.single_mem_supported _ _ rfl
      exact Q.ginzburgCutComponent_comp k hp (Q.ginzburgGeneratorDifferential_cut k φ a)
    · apply Submodule.smul_mem
      have ha : Finsupp.single (Q.ginzburgArrowPath a) (1:k) ∈
          Q.ginzburgCutComponent k _ _ (a.cutDegree Q) := by
        apply Finsupp.single_mem_supported
        simp [ginzburgArrowPath,cutDegree]
      exact Q.ginzburgCutComponent_comp k ih ha

theorem ginzburgDifferential_degree (φ : Q.Potential k) {u v : Q.Vertex} (q : ℤ)
    {f : Q.GinzburgPathComponent k u v} (hf : f ∈ Q.ginzburgCohomologicalComponent k u v q) :
    Q.ginzburgDifferential k φ u v f ∈ Q.ginzburgCohomologicalComponent k u v (q+1) := by
  change f ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    simp only [ginzburgDifferential_single,one_smul]
    change p.cohomologicalDegree=q at hp
    simpa only [hp] using p.differential_degree Q k φ
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

theorem ginzburgDifferential_cut (φ : Q.Potential k) {u v : Q.Vertex} (c : ℤ)
    {f : Q.GinzburgPathComponent k u v} (hf : f ∈ Q.ginzburgCutComponent k u v c) :
    Q.ginzburgDifferential k φ u v f ∈ Q.ginzburgCutComponent k u v c := by
  change f ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    simp only [ginzburgDifferential_single,one_smul]
    change p.cutDegree=c at hp
    simpa only [hp] using p.differential_cut Q k φ
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

theorem GinzburgPath.differential_winding (φ : Q.Potential k) {u v : Q.Vertex}
    (p : Q.GinzburgPath u v) :
    p.differential Q k φ ∈ Q.ginzburgWindingComponent k u v p.winding := by
  rw [p.winding_formula]
  exact Q.ginzburgCutComponent_le_winding k _ _ _ (p.differential_cut Q k φ)

end ASGinzburg.CutQuiver
