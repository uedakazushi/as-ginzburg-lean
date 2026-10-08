import ASGinzburg.GinzburgAugmentationBasis
import ASGinzburg.GinzburgDifferentialGradings
import ASGinzburg.GinzburgSquareZero

/-! The genuine nonempty-path augmentation ideal is closed under both
products and under the actual signed differential. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

theorem GinzburgPath.length_comp {u v w : Q.Vertex}
    (p : Q.GinzburgPath u v) (q : Q.GinzburgPath v w) :
    (p.comp q).length=p.length+q.length := by
  rw [←(p.comp q).length_toList,GinzburgPath.toList_comp,List.length_append,
    p.length_toList,q.length_toList]

universe u
variable (k : Type u) [Field k]

theorem ginzburgAugmentationSubmodule_comp_left {u v w : Q.Vertex}
    {f : Q.GinzburgPathComponent k u v} (hf : f ∈ Q.ginzburgAugmentationSubmodule k u v)
    (g : Q.GinzburgPathComponent k v w) :
    Q.ginzburgPathComp k g f ∈ Q.ginzburgAugmentationSubmodule k u w := by
  apply Q.ginzburgSupported_comp k {p | 0<p.length} Set.univ {p | 0<p.length} _ hf
    (by rw [Finsupp.supported_univ]; trivial)
  intro p hp q _hq
  change 0<p.length at hp
  change 0<(p.comp q).length
  rw [p.length_comp Q q]
  omega

theorem ginzburgAugmentationSubmodule_comp_right {u v w : Q.Vertex}
    {g : Q.GinzburgPathComponent k v w} (hg : g ∈ Q.ginzburgAugmentationSubmodule k v w)
    (f : Q.GinzburgPathComponent k u v) :
    Q.ginzburgPathComp k g f ∈ Q.ginzburgAugmentationSubmodule k u w := by
  apply Q.ginzburgSupported_comp k Set.univ {p | 0<p.length} {p | 0<p.length} _
    (by rw [Finsupp.supported_univ]; trivial) hg
  intro p _hp q hq
  change 0<q.length at hq
  change 0<(p.comp q).length
  rw [p.length_comp Q q]
  omega

theorem GinzburgPath.differential_mem_augmentation (φ : Q.Potential k) {u v : Q.Vertex}
    (p : Q.GinzburgPath u v) (hp : 0<p.length) :
    p.differential Q k φ ∈ Q.ginzburgAugmentationSubmodule k u v := by
  have hm : {q : Q.GinzburgPath u v | q.winding=p.winding} ⊆ {q | 0<q.length} := by
    intro q hq
    have hw := p.winding_pos_of_length_pos hp
    cases q with
    | nil => simp [GinzburgPath.winding] at hq; omega
    | snoc q a h => simp [GinzburgPath.length]
  exact Finsupp.supported_mono hm (p.differential_winding Q k φ)

theorem ginzburgDifferential_mem_augmentation (φ : Q.Potential k) {u v : Q.Vertex}
    {f : Q.GinzburgPathComponent k u v} (hf : f ∈ Q.ginzburgAugmentationSubmodule k u v) :
    Q.ginzburgDifferential k φ u v f ∈ Q.ginzburgAugmentationSubmodule k u v := by
  change f ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    simp only [Q.ginzburgDifferential_single,one_smul]
    exact p.differential_mem_augmentation Q k φ hp
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

noncomputable def ginzburgAugmentationDifferential (φ : Q.Potential k) (u v : Q.Vertex) :
    Q.ginzburgAugmentationSubmodule k u v →ₗ[k] Q.ginzburgAugmentationSubmodule k u v :=
  ((Q.ginzburgDifferential k φ u v).comp
    (Q.ginzburgAugmentationSubmodule k u v).subtype).codRestrict _
      (fun f => Q.ginzburgDifferential_mem_augmentation k φ f.property)

theorem ginzburgAugmentationDifferential_square (φ : Q.Potential k) (u v : Q.Vertex) :
    (Q.ginzburgAugmentationDifferential k φ u v).comp
      (Q.ginzburgAugmentationDifferential k φ u v)=0 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  exact Q.ginzburgDifferential_square k φ f.val

end ASGinzburg.CutQuiver
