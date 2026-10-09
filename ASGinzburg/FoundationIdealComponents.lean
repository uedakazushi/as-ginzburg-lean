import ASGinzburg.FoundationBlockIdeals
import ASGinzburg.FiniteComponentDecomposition

/-! Membership of a genuine component embedding in a restricted
foundation ideal is exactly membership of its original component. -/
namespace ASGinzburg.ZAlgebra
universe u
variable {k : Type u} [Field k] {B : ZAlgebra.{u,u} k}
  (I : B.LinearIdeal) (Q : CutQuiver)

theorem LinearIdeal.foundationIdeal_component_mem_iff (i j : Q.Vertex)
    (f : B.Hom (i.val : ℤ) (j.val : ℤ)) :
    (B.foundationComponents Q).totalComponent i j f ∈ I.foundationIdeal Q ↔
      f ∈ I.hom (i.val : ℤ) (j.val : ℤ) := by
  classical
  constructor
  · intro h
    have hx := h i j
    rw [(B.foundationComponents Q).totalComponent_apply_same] at hx
    exact hx
  · intro h p q
    by_cases hp : p=i
    · subst p
      by_cases hq : q=j
      · subst q
        rw [(B.foundationComponents Q).totalComponent_apply_same]
        exact h
      · change ((B.foundationComponents Q).totalComponent i j f) i q ∈ I.hom (i.val : ℤ) (q.val : ℤ)
        simp [LinearComponentAlgebra.totalComponent,hq]
    · rw [(B.foundationComponents Q).totalComponent_apply_source_ne i j p q f hp]
      exact (I.hom (p.val : ℤ) (q.val : ℤ)).zero_mem

end ASGinzburg.ZAlgebra
