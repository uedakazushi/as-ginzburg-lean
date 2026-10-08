import ASGinzburg.GinzburgGeneratorDifferentials

/-! The genuine generator differentials preserve both internal gradings. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

@[simp] theorem GinzburgPath.cutDegree_transport {u v u' v' : Q.Vertex}
    (hu : u=u') (hv : v=v') (p : Q.GinzburgPath u v) :
    (p.transport Q hu hv).cutDegree=p.cutDegree := by subst u' v'; rfl

theorem Path.originalGinzburg_cutDegree {u v : Q.Vertex} (p : Q.Path u v) :
    (p.originalGinzburg Q).cutDegree=p.cutDegree := by
  induction p with
  | nil => simp [originalGinzburg,GinzburgPath.cutDegree,Path.cutDegree]
  | snoc p a h ih =>
    simp [originalGinzburg,GinzburgPath.cutDegree,Path.cutDegree,GinzburgArrow.cutDegree,ih]

def ginzburgCutComponent (u v : Q.Vertex) (c : ℤ) :
    Submodule k (Q.GinzburgPathComponent k u v) :=
  Finsupp.supported k k {p | p.cutDegree=c}

def ginzburgWindingComponent (u v : Q.Vertex) (w : ℤ) :
    Submodule k (Q.GinzburgPathComponent k u v) :=
  Finsupp.supported k k {p | p.winding=w}

theorem originalGinzburgLinearMap_cut {u v : Q.Vertex} {c : ℤ}
    {f : Q.PathComponent k u v}
    (hf : f ∈ Finsupp.supported k k {p : Q.Path u v | (p.cutDegree:ℤ)=c}) :
    Q.originalGinzburgLinearMap k u v f ∈ Q.ginzburgCutComponent k u v c := by
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    rw [Q.originalGinzburgLinearMap_single]
    apply Finsupp.single_mem_supported
    simpa only [Set.mem_setOf_eq,Path.originalGinzburg_cutDegree] using hp
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

theorem ginzburgLoopDifferential_cut (v : Q.Vertex) :
    Q.ginzburgLoopDifferential k v ∈ Q.ginzburgCutComponent k v v 1 := by
  unfold ginzburgLoopDifferential
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sub_mem
  · split_ifs with ht
    · apply Finsupp.single_mem_supported
      simp [GinzburgPath.cutDegree_comp,originalGinzburgArrowPath,dualGinzburgArrowPath,
        GinzburgPath.cutDegree,GinzburgArrow.cutDegree]
    · exact Submodule.zero_mem _
  · split_ifs with hs
    · apply Finsupp.single_mem_supported
      simp [GinzburgPath.cutDegree_comp,originalGinzburgArrowPath,dualGinzburgArrowPath,
        GinzburgPath.cutDegree,GinzburgArrow.cutDegree]
    · exact Submodule.zero_mem _

theorem ginzburgGeneratorDifferential_cut (φ : Q.Potential k) (a : Q.GinzburgArrow) :
    Q.ginzburgGeneratorDifferential k φ a ∈
      Q.ginzburgCutComponent k (a.source Q) (a.target Q) (a.cutDegree Q) := by
  cases a with
  | original a => exact Submodule.zero_mem _
  | dual a =>
    apply Q.originalGinzburgLinearMap_cut k
    apply Finsupp.supported_mono _ (Q.pathCyclicDerivative_supported_degrees k a φ)
    rintro p ⟨_,hp⟩
    change (p.cutDegree:ℤ)=1-(Q.cutDegree a:ℤ)
    have hi : (p.cutDegree:ℤ)+(Q.cutDegree a:ℤ)=1 := by exact_mod_cast hp
    omega
  | loop v => exact Q.ginzburgLoopDifferential_cut k v

theorem ginzburgCutComponent_le_winding (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgCutComponent k u v c ≤
      Q.ginzburgWindingComponent k u v ((v.val:ℤ)-u.val+Q.vertices*c) := by
  apply Finsupp.supported_mono
  intro p hp
  change p.cutDegree=c at hp
  change p.winding=_
  rw [p.winding_formula,hp]

theorem ginzburgGeneratorDifferential_winding (φ : Q.Potential k) (a : Q.GinzburgArrow) :
    Q.ginzburgGeneratorDifferential k φ a ∈
      Q.ginzburgWindingComponent k (a.source Q) (a.target Q) (a.winding Q) := by
  rw [a.winding_formula Q]
  exact Q.ginzburgCutComponent_le_winding k _ _ _ (Q.ginzburgGeneratorDifferential_cut k φ a)

end ASGinzburg.CutQuiver
