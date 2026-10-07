import Mathlib.Tactic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The finite cut quiver and its unrolled vertices

Concrete definitions for §1.1 of the source. No periodicity of an algebra
is included in `CutQuiver`; the permutation below only permutes vertices.
-/

namespace ASGinzburg

structure CutQuiver where
  vertices : ℕ
  arrows : ℕ
  at_least_three : 3 ≤ vertices
  source : Fin arrows → Fin vertices
  target : Fin arrows → Fin vertices
  cut : Fin arrows → Bool
  forward : ∀ a, cut a = false → (source a).val < (target a).val
  backward : ∀ a, cut a = true → (target a).val < (source a).val

namespace CutQuiver

variable (Q : CutQuiver)

abbrev Arrow := Fin Q.arrows
abbrev Vertex := Fin Q.vertices
abbrev LiftVertex := Q.Vertex × ℤ

def cutDegree (a : Q.Arrow) : ℕ := if Q.cut a then 1 else 0

def winding (a : Q.Arrow) : ℤ :=
  (Q.target a).val - (Q.source a).val + Q.vertices * Q.cutDegree a

def height (v : Q.LiftVertex) : ℤ := v.1.val + Q.vertices * v.2

instance periodNeZero : NeZero Q.vertices := ⟨by have := Q.at_least_three; omega⟩

def heightEquiv : Q.LiftVertex ≃ ℤ :=
  (Equiv.prodComm Q.Vertex ℤ).trans (Int.divModEquiv Q.vertices).symm

theorem heightEquiv_apply (v : Q.LiftVertex) : Q.heightEquiv v = Q.height v := by
  change v.2 * Q.vertices + (v.1.val : ℤ) = v.1.val + Q.vertices * v.2
  ring

theorem height_bijective : Function.Bijective Q.height := by
  have hfun : Q.height = Q.heightEquiv := funext fun v => (Q.heightEquiv_apply v).symm
  rw [hfun]
  exact Q.heightEquiv.bijective

def shift (r : ℤ) (v : Q.LiftVertex) : Q.LiftVertex := (v.1, v.2 + r)

def tau : Q.LiftVertex ≃ Q.LiftVertex where
  toFun := Q.shift 1
  invFun := Q.shift (-1)
  left_inv := by intro v; simp [shift]
  right_inv := by intro v; simp [shift]

def liftedSource (a : Q.Arrow) (m : ℤ) : Q.LiftVertex := (Q.source a, m)
def liftedTarget (a : Q.Arrow) (m : ℤ) : Q.LiftVertex :=
  (Q.target a, m + Q.cutDegree a)

@[simp] theorem cutDegree_false {a : Q.Arrow} (h : Q.cut a = false) :
    Q.cutDegree a = 0 := by simp [cutDegree, h]

@[simp] theorem cutDegree_true {a : Q.Arrow} (h : Q.cut a = true) :
    Q.cutDegree a = 1 := by simp [cutDegree, h]

theorem winding_pos (a : Q.Arrow) : 0 < Q.winding a := by
  cases h : Q.cut a
  · have := Q.forward a h
    simp only [winding, cutDegree_false Q h, Nat.cast_zero, mul_zero, add_zero]
    omega
  · have := Q.backward a h
    have := (Q.source a).isLt
    simp only [winding, cutDegree_true Q h, Nat.cast_one, mul_one]
    omega

theorem winding_lt_period (a : Q.Arrow) : Q.winding a < Q.vertices := by
  cases h : Q.cut a
  · have := (Q.target a).isLt
    simp only [winding, cutDegree_false Q h, Nat.cast_zero, mul_zero, add_zero]
    omega
  · have := Q.backward a h
    simp only [winding, cutDegree_true Q h, Nat.cast_one, mul_one]
    omega

@[simp] theorem height_shift (r : ℤ) (v : Q.LiftVertex) :
    Q.height (Q.shift r v) = Q.height v + Q.vertices * r := by
  simp only [height, shift]
  ring

@[simp] theorem height_tau (v : Q.LiftVertex) :
    Q.height (Q.tau v) = Q.height v + Q.vertices := by
  change Q.height (Q.shift 1 v) = Q.height v + Q.vertices
  rw [height_shift, mul_one]

theorem lifted_height_difference (a : Q.Arrow) (m : ℤ) :
    Q.height (Q.liftedTarget a m) - Q.height (Q.liftedSource a m) = Q.winding a := by
  simp only [height, liftedSource, liftedTarget, winding]
  ring

theorem lifted_arrow_increases_height (a : Q.Arrow) (m : ℤ) :
    Q.height (Q.liftedSource a m) < Q.height (Q.liftedTarget a m) := by
  have := Q.winding_pos a
  rw [← Q.lifted_height_difference a m] at this
  omega

theorem intermediate_in_interval {l r u v w : ℤ}
    (hu : l ≤ u) (hw : w ≤ r) (huv : u ≤ v) (hvw : v ≤ w) :
    l ≤ v ∧ v ≤ r := by omega

/-- Finite directed paths, with the source and target checked in the type. -/
inductive Path : Q.Vertex → Q.Vertex → Type
  | nil (v : Q.Vertex) : Path v v
  | snoc {u v : Q.Vertex} (p : Path u v) (a : Q.Arrow)
      (h : Q.source a = v) : Path u (Q.target a)

namespace Path

variable {Q}

def length {u v : Q.Vertex} : Q.Path u v → ℕ
  | .nil _ => 0
  | .snoc p _ _ => length p + 1

def cutDegree {u v : Q.Vertex} : Q.Path u v → ℕ
  | .nil _ => 0
  | .snoc p a _ => cutDegree p + Q.cutDegree a

def winding {u v : Q.Vertex} : Q.Path u v → ℤ
  | .nil _ => 0
  | .snoc p a _ => winding p + Q.winding a

def toList {u v : Q.Vertex} : Q.Path u v → List Q.Arrow
  | .nil _ => []
  | .snoc p a _ => toList p ++ [a]

theorem length_toList {u v : Q.Vertex} (p : Q.Path u v) : p.toList.length = p.length := by
  induction p with
  | nil => rfl
  | snoc p a h ih => simp [toList, length, ih]

theorem winding_eq {u v : Q.Vertex} (p : Q.Path u v) :
    p.winding = (v.val : ℤ) - u.val + Q.vertices * p.cutDegree := by
  induction p with
  | nil => simp [winding, cutDegree]
  | snoc p a h ih =>
    simp only [winding, cutDegree, Nat.cast_add, ih, CutQuiver.winding, h]
    ring

theorem winding_nonneg {u v : Q.Vertex} (p : Q.Path u v) : 0 ≤ p.winding := by
  induction p with
  | nil => simp [winding]
  | snoc p a h ih =>
    have := Q.winding_pos a
    simp only [winding]
    omega

theorem winding_pos_of_length_pos {u v : Q.Vertex} (p : Q.Path u v)
    (hp : 0 < p.length) : 0 < p.winding := by
  cases p with
  | nil => simp [length] at hp
  | snoc p a h =>
    have := p.winding_nonneg
    have := Q.winding_pos a
    simp only [winding]
    omega

theorem zero_cut_increases_vertex {u v : Q.Vertex} (p : Q.Path u v)
    (hl : 0 < p.length) (hc : p.cutDegree = 0) : u.val < v.val := by
  have := p.winding_pos_of_length_pos hl
  rw [p.winding_eq, hc] at this
  simp only [Nat.cast_zero, mul_zero, add_zero] at this
  omega

theorem zero_cut_has_no_nonempty_cycle {u : Q.Vertex} (p : Q.Path u u)
    (hc : p.cutDegree = 0) : p.length = 0 := by
  by_contra h
  have := p.zero_cut_increases_vertex (by omega) hc
  omega

theorem cut_one_cycle_winding {u : Q.Vertex} (p : Q.Path u u)
    (hc : p.cutDegree = 1) : p.winding = Q.vertices := by
  simp [p.winding_eq, hc]

end Path
end CutQuiver
end ASGinzburg
