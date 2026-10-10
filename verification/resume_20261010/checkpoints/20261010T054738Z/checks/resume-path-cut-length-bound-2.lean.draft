import ASGinzburg.PathCutGrading
import ASGinzburg.PathLengthFiltration

/-! Strictly positive arrow winding bounds the length of every actual
homogeneous path, so each fixed cut component has a finite length filtration. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem Path.length_le_winding {i j : Q.Vertex} (p : Q.Path i j) :
    (p.length : ℤ) ≤ p.winding := by
  induction p with
  | nil => simp [Path.length,Path.winding]
  | snoc p a ha ih =>
    have h := Q.winding_pos a
    simp only [Path.length,Path.winding,Nat.cast_add,Nat.cast_one]
    omega

theorem pathCut_lengthFiltration_eq_zero (i j : Q.Vertex) (c : ℤ) (n : ℕ)
    (hn : (j.val : ℤ) - i.val + Q.vertices * c < n)
    (f : Q.PathComponent k i j) (hc : f ∈ Q.pathCutComponent k i j c)
    (hl : f ∈ Q.pathLengthFiltration k n i j) : f = 0 := by
  classical
  apply Finsupp.ext
  intro p
  by_contra h
  have hp : p ∈ f.support := by simpa using h
  have Hc := (Finsupp.mem_supported k f).mp hc hp
  have Hl := (Finsupp.mem_supported k f).mp hl hp
  have Hw := Path.length_le_winding Q p
  change (p.cutDegree : ℤ) = c at Hc
  change n ≤ p.length at Hl
  rw [p.winding_eq,Hc] at Hw
  simp only [Finsupp.zero_apply] at h
  omega

end ASGinzburg.CutQuiver
