import ASGinzburg.GinzburgLeibniz
import ASGinzburg.GinzburgDifferentialGradings

/-! The parity operator and the degree-one differential anticommute. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgSign_succ (q : ℤ) : ginzburgSign k (q+1)=-ginzburgSign k q := by
  rw [ginzburgSign_add]
  simp [ginzburgSign]

theorem ginzburgSignMap_homogeneous {u v : Q.Vertex} {q : ℤ}
    {f : Q.GinzburgPathComponent k u v} (hf : f ∈ Q.ginzburgCohomologicalComponent k u v q) :
    Q.ginzburgSignMap k u v f=ginzburgSign k q • f := by
  change f ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    change p.cohomologicalDegree=q at hp
    simp only [ginzburgSignMap_single,hp]
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add,ihx,ihy,smul_add]
  | smul a x hx ih =>
    rw [map_smul,ih]
    exact smul_comm a (ginzburgSign k q) x

theorem ginzburgDifferential_sign (φ : Q.Potential k) {u v : Q.Vertex}
    (f : Q.GinzburgPathComponent k u v) :
    Q.ginzburgDifferential k φ u v (Q.ginzburgSignMap k u v f)=
      -(Q.ginzburgSignMap k u v (Q.ginzburgDifferential k φ u v f)) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add,hf,hg]
    abel
  | single p c =>
    simp only [ginzburgSignMap_single,ginzburgDifferential_single,map_smul]
    rw [Q.ginzburgSignMap_homogeneous k (p.differential_degree Q k φ),ginzburgSign_succ]
    simp only [neg_smul,smul_neg,smul_smul,mul_comm,neg_neg]

theorem ginzburgDifferential_comp_homogeneous (φ : Q.Potential k) {u v w : Q.Vertex}
    (f : Q.GinzburgPathComponent k u v) (g : Q.GinzburgPathComponent k v w) (q : ℤ)
    (hg : g ∈ Q.ginzburgCohomologicalComponent k v w q) :
    Q.ginzburgDifferential k φ u w (Q.ginzburgPathComp k g f)=
      Q.ginzburgPathComp k (Q.ginzburgDifferential k φ v w g) f+
      ginzburgSign k q • Q.ginzburgPathComp k g (Q.ginzburgDifferential k φ u v f) := by
  rw [Q.ginzburgDifferential_comp k φ f g,Q.ginzburgSignMap_homogeneous k hg]
  simp only [map_smul,LinearMap.smul_apply]

end ASGinzburg.CutQuiver
