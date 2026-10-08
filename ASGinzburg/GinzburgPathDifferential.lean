import ASGinzburg.GinzburgGeneratorDifferentials
import Mathlib.Algebra.Field.Power

/-! The signed extension of (1.3) to actual finite paths. Square-zero
and the full graded Leibniz theorem are proved separately. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgSign (q : ℤ) : k := (-1:k)^q

@[simp] theorem ginzburgSign_zero : ginzburgSign k 0=1 := by simp [ginzburgSign]

theorem ginzburgSign_add (q r : ℤ) :
    ginzburgSign k (q+r)=ginzburgSign k q*ginzburgSign k r :=
  zpow_add₀ (neg_ne_zero.mpr one_ne_zero) q r

def ginzburgArrowPath (a : Q.GinzburgArrow) :
    Q.GinzburgPath (a.source Q) (a.target Q) := .snoc (.nil (a.source Q)) a rfl

noncomputable def GinzburgPath.differential (φ : Q.Potential k) :
    {u v : Q.Vertex} → Q.GinzburgPath u v → Q.GinzburgPathComponent k u v
  | _,_,.nil _ => 0
  | _,_,.snoc p a h =>
    Q.ginzburgPathComp k (h ▸ Q.ginzburgGeneratorDifferential k φ a) (Finsupp.single p 1)+
      ginzburgSign k (a.cohomologicalDegree Q) •
        Q.ginzburgPathComp k (h ▸ Finsupp.single (Q.ginzburgArrowPath a) 1) (p.differential φ)
termination_by u v p => p.length
decreasing_by simp_all [GinzburgPath.length]

noncomputable def ginzburgDifferential (φ : Q.Potential k) (u v : Q.Vertex) :
    Q.GinzburgPathComponent k u v →ₗ[k] Q.GinzburgPathComponent k u v :=
  Finsupp.linearCombination k (GinzburgPath.differential Q k φ)

@[simp] theorem ginzburgDifferential_single (φ : Q.Potential k) {u v : Q.Vertex}
    (p : Q.GinzburgPath u v) (c : k) :
    Q.ginzburgDifferential k φ u v (Finsupp.single p c)=c • p.differential Q k φ := by
  simp [ginzburgDifferential]

@[simp] theorem GinzburgPath.differential_nil (φ : Q.Potential k) (v : Q.Vertex) :
    (GinzburgPath.nil v).differential Q k φ=0 := by simp [differential]

theorem ginzburgDifferential_id (φ : Q.Potential k) (v : Q.Vertex) :
    Q.ginzburgDifferential k φ v v (Q.ginzburgPathId k v)=0 := by
  simp [ginzburgPathId]

theorem ginzburgDifferential_generator (φ : Q.Potential k) (a : Q.GinzburgArrow) :
    Q.ginzburgDifferential k φ (a.source Q) (a.target Q)
      (Finsupp.single (Q.ginzburgArrowPath a) 1)=Q.ginzburgGeneratorDifferential k φ a := by
  simp only [ginzburgDifferential_single,one_smul,ginzburgArrowPath,GinzburgPath.differential,
    map_zero,smul_zero,add_zero]
  exact Q.id_ginzburgPathComp k _

end ASGinzburg.CutQuiver
