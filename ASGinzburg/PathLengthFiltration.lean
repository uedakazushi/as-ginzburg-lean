import ASGinzburg.PathLinearIdeals
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! The length filtration and its genuine two-sided path ideals. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

@[simp] theorem Path.length_comp {u v w : Q.Vertex}
    (p : Q.Path u v) (q : Q.Path v w) :
    (p.comp q).length = p.length + q.length := by
  induction q with
  | nil => simp [Path.comp, Path.length]
  | snoc q a h ih => simp [Path.comp, Path.length, ih, Nat.add_assoc]

def pathLengthFiltration (n : ℕ) (u v : Q.Vertex) :
    Submodule k (Q.PathComponent k u v) :=
  Finsupp.supported k k {p : Q.Path u v | n ≤ p.length}

theorem pathComp_mem_lengthFiltration {u v w : Q.Vertex} {m n : ℕ}
    {f : Q.PathComponent k u v} (hf : f ∈ Q.pathLengthFiltration k m u v)
    {g : Q.PathComponent k v w} (hg : g ∈ Q.pathLengthFiltration k n v w) :
    Q.pathComp k g f ∈ Q.pathLengthFiltration k (m+n) u w := by
  change f ∈ Finsupp.supported k k _ at hf
  change g ∈ Finsupp.supported k k _ at hg
  rw [Finsupp.supported_eq_span_single] at hf hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q,hq,rfl⟩ := hx
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p,hp,rfl⟩ := hx
      rw [Q.pathComp_single]
      apply Finsupp.single_mem_supported
      change m+n ≤ (p.comp q).length
      rw [Path.length_comp]
      exact Nat.add_le_add hp hq
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
      simpa only [map_smul] using Submodule.smul_mem _ a ih
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add,LinearMap.add_apply] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    simpa only [map_smul,LinearMap.smul_apply] using Submodule.smul_mem _ a ih

theorem mem_pathLengthFiltration_zero {u v : Q.Vertex}
    (f : Q.PathComponent k u v) : f ∈ Q.pathLengthFiltration k 0 u v := by
  apply (Finsupp.mem_supported k f).mpr
  intro p _
  exact Nat.zero_le _

noncomputable def pathLengthIdeal (n : ℕ) : Q.PathLinearIdeal k where
  hom := Q.pathLengthFiltration k n
  comp_left := by
    intro u v w f hf g
    simpa only [Nat.add_zero] using Q.pathComp_mem_lengthFiltration k hf
      (Q.mem_pathLengthFiltration_zero k g)
  comp_right := by
    intro u v w g hg f
    simpa only [Nat.zero_add] using Q.pathComp_mem_lengthFiltration k
      (Q.mem_pathLengthFiltration_zero k f) hg

end ASGinzburg.CutQuiver
