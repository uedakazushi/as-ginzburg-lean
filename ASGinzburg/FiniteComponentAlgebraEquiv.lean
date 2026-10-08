import ASGinzburg.FiniteComponentAlgebra
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Algebra.Equiv

/-! Actual component isomorphisms induce isomorphisms of the finite
unital convolution algebras. -/
namespace ASGinzburg.LinearComponentAlgebra
universe u v
variable {k : Type u} [Field k] {ι : Type v} [Fintype ι]
variable (B C : LinearComponentAlgebra k ι)

structure Isomorphism where
  map : ∀ i j, B.Hom i j ≃ₗ[k] C.Hom i j
  map_id : ∀ i, map i i (B.id i)=C.id i
  map_comp : ∀ {i j l} (f : B.Hom i j) (g : B.Hom j l),
    map i l (B.comp g f)=C.comp (map j l g) (map i j f)

namespace Isomorphism
variable {B C} (E : B.Isomorphism C)

noncomputable def totalLinearEquiv : B.Total ≃ₗ[k] C.Total :=
  LinearEquiv.piCongrRight fun i => LinearEquiv.piCongrRight fun j => E.map i j

omit [Fintype ι] in
theorem totalLinearEquiv_one : E.totalLinearEquiv (1 : B.Total)=(1 : C.Total) := by
  classical
  funext i j
  change E.map i j (B.totalOne i j)=C.totalOne i j
  by_cases h : i=j
  · subst j
    rw [B.totalOne_diag,C.totalOne_diag,E.map_id]
  · rw [B.totalOne_offdiag h,C.totalOne_offdiag h,map_zero]

theorem totalLinearEquiv_mul (x y : B.Total) :
    E.totalLinearEquiv (x*y)=E.totalLinearEquiv x*E.totalLinearEquiv y := by
  funext i l
  change E.map i l (∑ j, B.comp (x j l) (y i j))=
    ∑ j, C.comp (E.map j l (x j l)) (E.map i j (y i j))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact E.map_comp _ _

noncomputable def totalAlgEquiv : B.Total ≃ₐ[k] C.Total :=
  AlgEquiv.ofLinearEquiv E.totalLinearEquiv E.totalLinearEquiv_one E.totalLinearEquiv_mul

end Isomorphism
end ASGinzburg.LinearComponentAlgebra
