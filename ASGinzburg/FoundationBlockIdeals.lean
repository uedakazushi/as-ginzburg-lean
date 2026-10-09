import ASGinzburg.FoundationAlgebra
import ASGinzburg.ZAlgebraHomomorphisms
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! A genuine two-sided component ideal restricts to a two-sided
ideal of the actual finite foundation convolution ring. -/
namespace ASGinzburg.ZAlgebra
universe u
variable {k : Type u} [Field k] {B : ZAlgebra.{u,u} k}
  (I : B.LinearIdeal) (Q : CutQuiver)

noncomputable def LinearIdeal.foundationIdeal : Ideal (B.FoundationAlgebra Q) where
  carrier := {x | ∀ i j : Q.Vertex,x i j ∈ I.hom (i.val : ℤ) (j.val : ℤ)}
  zero_mem' := fun i j => (I.hom _ _).zero_mem
  add_mem' := fun hx hy i j => (I.hom _ _).add_mem (hx i j) (hy i j)
  smul_mem' := by
    intro a x hx i l
    change (∑ j : Q.Vertex,B.comp (a j l) (x i j)) ∈ I.hom (i.val : ℤ) (l.val : ℤ)
    apply Submodule.sum_mem
    intro j _
    exact I.comp_left (hx i j) (a j l)

@[simp] theorem LinearIdeal.mem_foundationIdeal
    (x : B.FoundationAlgebra Q) :
    x ∈ I.foundationIdeal Q ↔ ∀ i j : Q.Vertex,x i j ∈ I.hom (i.val : ℤ) (j.val : ℤ) := Iff.rfl

noncomputable instance LinearIdeal.foundationIdealIsTwoSided : (I.foundationIdeal Q).IsTwoSided where
  mul_mem_of_left := by
    intro x a hx i l
    change (∑ j : Q.Vertex,B.comp (x j l) (a i j)) ∈ I.hom (i.val : ℤ) (l.val : ℤ)
    apply Submodule.sum_mem
    intro j _
    exact I.comp_right (hx j l) (a i j)

end ASGinzburg.ZAlgebra
