import ASGinzburg.PathAlgebra
import ASGinzburg.CyclicDerivative
import ASGinzburg.Tensor333

/-!
# The three-vertex, three-arrow-per-edge quiver in Corollary 5.2

The winding degree of every arrow is one. Consequently every closed
cut-degree-one path has length exactly three, and a path of the same
degrees as an arrow has length one. This checks the cubic-only and
linear-change-of-arrow assertions used in the corollary.
-/

namespace ASGinzburg

def triangle333 : CutQuiver where
  vertices := 3
  arrows := 9
  at_least_three := le_rfl
  source a := ⟨a.val / 3, by omega⟩
  target a := ⟨(a.val / 3 + 1) % 3, by omega⟩
  cut a := decide (6 ≤ a.val)
  forward := by
    intro a h
    have hc : ¬6 ≤ a.val := of_decide_eq_false h
    dsimp
    have := a.isLt
    omega
  backward := by
    intro a h
    simp only [decide_eq_true_eq] at h
    dsimp
    have := a.isLt
    omega

def triangleX (i : Fin 3) : triangle333.Arrow := ⟨i.val, by change i.val < 9; omega⟩
def triangleY (i : Fin 3) : triangle333.Arrow := ⟨3 + i.val, by change 3 + i.val < 9; omega⟩
def triangleZ (i : Fin 3) : triangle333.Arrow := ⟨6 + i.val, by change 6 + i.val < 9; omega⟩

@[simp] theorem triangleX_cut (i : Fin 3) : triangle333.cut (triangleX i) = false := by
  simp [triangle333, triangleX]
  omega

@[simp] theorem triangleY_cut (i : Fin 3) : triangle333.cut (triangleY i) = false := by
  simp [triangle333, triangleY]
  omega

@[simp] theorem triangleZ_cut (i : Fin 3) : triangle333.cut (triangleZ i) = true := by
  simp [triangle333, triangleZ]

theorem triangle_arrow_winding (a : triangle333.Arrow) : triangle333.winding a = 1 := by
  cases h : triangle333.cut a
  · have hc : ¬6 ≤ a.val := of_decide_eq_false h
    simp only [CutQuiver.winding, CutQuiver.cutDegree_false _ h, Nat.cast_zero,
      mul_zero, add_zero]
    dsimp [triangle333]
    have ha : a.val < 9 := a.isLt
    omega
  · have hc : 6 ≤ a.val := by simpa only [triangle333, decide_eq_true_eq] using h
    simp only [CutQuiver.winding, CutQuiver.cutDegree_true _ h, Nat.cast_one, mul_one]
    dsimp [triangle333]
    have ha : a.val < 9 := a.isLt
    omega

theorem triangle_path_winding {u v : triangle333.Vertex} (p : triangle333.Path u v) :
    p.winding = p.length := by
  induction p with
  | nil => rfl
  | snoc p a h ih =>
    simp [CutQuiver.Path.winding, CutQuiver.Path.length, ih, triangle_arrow_winding]

theorem triangle_cut_one_cycle_is_cubic {v : triangle333.Vertex} (p : triangle333.Path v v)
    (hc : p.cutDegree = 1) : p.length = 3 := by
  have hp := p.cut_one_cycle_winding hc
  rw [triangle_path_winding] at hp
  change (p.length : ℤ) = 3 at hp
  omega

theorem triangle_same_winding_as_arrow_is_linear {u v : triangle333.Vertex}
    (a : triangle333.Arrow) (p : triangle333.Path u v) (h : p.winding = triangle333.winding a) :
    p.length = 1 := by
  rw [triangle_path_winding, triangle_arrow_winding] at h
  omega

universe u
variable {k : Type u} [Field k]

noncomputable def trianglePotential (c : CubicCoefficients333 k) :
    WordPolynomial k triangle333.Arrow :=
  ∑ xyz : Triple333, Finsupp.single
    [triangleX xyz.1, triangleY xyz.2.1, triangleZ xyz.2.2] (c xyz)

theorem trianglePotential_cut_derivative_identity (c : CubicCoefficients333 k) :
    cyclicCutReconstruction triangle333.cut (cyclicTrace (trianglePotential c)) =
      cyclicTrace (trianglePotential c) := by
  classical
  simp only [trianglePotential, map_sum, cyclicTrace, Finsupp.linearCombination_single]
  apply Finset.sum_congr rfl
  intro xyz _
  simp [cyclicCutReconstruction_traceWord, reconstructAux_euler, wordCutDegree]

end ASGinzburg
