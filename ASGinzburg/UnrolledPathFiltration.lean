import ASGinzburg.UnrolledPathFiniteness
import ASGinzburg.UnrolledPathAlgebra
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! The length filtration on the genuine free unrolled path algebra. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

@[simp] theorem UnrolledPath.length_comp {u v w : Q.LiftVertex}
    (p : Q.UnrolledPath u v) (q : Q.UnrolledPath v w) :
    (p.comp q).length = p.length + q.length := by
  induction q with
  | nil => simp [UnrolledPath.comp,UnrolledPath.length]
  | snoc a q ih => simp [UnrolledPath.comp,UnrolledPath.length,ih,Nat.add_assoc]

def unrolledPathFiltration (n : ℕ) (u v : Q.LiftVertex) :
    Submodule k (Q.UnrolledPathComponent k u v) :=
  Finsupp.supported k k {p : Q.UnrolledPath u v | n ≤ p.length}

theorem unrolledPathComp_mem_filtration {u v w : Q.LiftVertex} {m n : ℕ}
    {f : Q.UnrolledPathComponent k u v} (hf : f ∈ Q.unrolledPathFiltration k m u v)
    {g : Q.UnrolledPathComponent k v w} (hg : g ∈ Q.unrolledPathFiltration k n v w) :
    Q.unrolledPathComp k g f ∈ Q.unrolledPathFiltration k (m+n) u w := by
  change f ∈ Finsupp.supported k k _ at hf
  change g ∈ Finsupp.supported k k _ at hg
  rw [Finsupp.supported_eq_span_single] at hf hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q,hq,rfl⟩ := hx
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p,hp,rfl⟩ := hx
      rw [Q.unrolledPathComp_single]
      apply Finsupp.single_mem_supported
      change m+n ≤ (p.comp q).length
      rw [UnrolledPath.length_comp]
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

theorem mem_unrolledPathFiltration_zero {u v : Q.LiftVertex}
    (f : Q.UnrolledPathComponent k u v) : f ∈ Q.unrolledPathFiltration k 0 u v := by
  apply (Finsupp.mem_supported k f).mpr
  intro p _
  exact Nat.zero_le _

theorem unrolledPath_long_factor {u v : Q.LiftVertex} (p : Q.UnrolledPath u v)
    (hp : 2 ≤ p.length) :
    ∃ w, ∃ f ∈ Q.unrolledPathFiltration k 1 u w,
      ∃ g ∈ Q.unrolledPathFiltration k 1 w v,
        Q.unrolledPathComp k g f = Finsupp.single p 1 := by
  cases p with
  | nil => simp [UnrolledPath.length] at hp
  | @snoc v a p =>
    have hp' : 1 ≤ p.length := by
      simp only [UnrolledPath.length] at hp
      omega
    refine ⟨Q.incomingSource v a,Finsupp.single p 1,?_,
      Finsupp.single (UnrolledPath.snoc a (.nil (Q.incomingSource v a))) 1,?_,?_⟩
    · exact Finsupp.single_mem_supported k (1:k) hp'
    · apply Finsupp.single_mem_supported
      simp [UnrolledPath.length]
    · simp [UnrolledPath.comp]

end ASGinzburg.CutQuiver
