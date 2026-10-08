import ASGinzburg.PathQuotientProducts
import Mathlib.Algebra.Algebra.Basic

/-! Finite families of actual linear morphism spaces form a unital ring
by genuine component composition and finite matrix convolution. -/
namespace ASGinzburg
universe u v

structure LinearComponentAlgebra (k : Type u) [Field k] (ι : Type v) where
  Hom : ι → ι → Type u
  [homAdd : ∀ i j, AddCommGroup (Hom i j)]
  [homModule : ∀ i j, Module k (Hom i j)]
  id : ∀ i, Hom i i
  comp : ∀ {i j l}, Hom j l →ₗ[k] Hom i j →ₗ[k] Hom i l
  comp_id : ∀ {i j} (f : Hom i j), comp (id j) f=f
  id_comp : ∀ {i j} (f : Hom i j), comp f (id i)=f
  comp_assoc : ∀ {i j l m} (f : Hom i j) (g : Hom j l) (h : Hom l m),
    comp h (comp g f)=comp (comp h g) f

attribute [instance] LinearComponentAlgebra.homAdd LinearComponentAlgebra.homModule

namespace LinearComponentAlgebra
variable {k : Type u} [Field k] {ι : Type v} [Fintype ι] (B : LinearComponentAlgebra k ι)

abbrev Total := ∀ i j, B.Hom i j

noncomputable def totalMul (x y : B.Total) : B.Total :=
  fun i l => ∑ j, B.comp (x j l) (y i j)

noncomputable def totalOne : B.Total := by
  classical
  exact fun i j => if h : i=j then h ▸ B.id i else 0

omit [Fintype ι] in
@[simp] theorem totalOne_diag (i : ι) : B.totalOne i i=B.id i := by
  classical
  simp [totalOne]

omit [Fintype ι] in
theorem totalOne_offdiag {i j : ι} (h : i≠j) : B.totalOne i j=0 := by
  classical
  simp [totalOne,h]

theorem totalOne_mul (x : B.Total) : B.totalMul B.totalOne x=x := by
  classical
  funext i l
  change (∑ j, B.comp (B.totalOne j l) (x i j))=x i l
  rw [Finset.sum_eq_single l]
  · rw [B.totalOne_diag,B.comp_id]
  · intro j hj h
    rw [B.totalOne_offdiag h]
    simp
  · simp

theorem totalMul_one (x : B.Total) : B.totalMul x B.totalOne=x := by
  classical
  funext i l
  change (∑ j, B.comp (x j l) (B.totalOne i j))=x i l
  rw [Finset.sum_eq_single i]
  · rw [B.totalOne_diag,B.id_comp]
  · intro j hj h
    rw [B.totalOne_offdiag (Ne.symm h),map_zero]
  · simp

theorem totalMul_assoc (x y z : B.Total) :
    B.totalMul (B.totalMul x y) z=B.totalMul x (B.totalMul y z) := by
  funext i l
  simp only [totalMul,map_sum,LinearMap.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro h hh
  exact (B.comp_assoc _ _ _).symm

theorem totalMul_add (x y z : B.Total) : B.totalMul x (y+z)=B.totalMul x y+B.totalMul x z := by
  funext i l
  simp [totalMul,map_add,Finset.sum_add_distrib]

theorem totalAdd_mul (x y z : B.Total) : B.totalMul (x+y) z=B.totalMul x z+B.totalMul y z := by
  funext i l
  simp [totalMul,map_add,LinearMap.add_apply,Finset.sum_add_distrib]

noncomputable instance totalMulInst : Mul B.Total := ⟨B.totalMul⟩

noncomputable instance totalOneInst : One B.Total := ⟨B.totalOne⟩

noncomputable instance totalRing : Ring B.Total where
  toAddCommGroup := inferInstance
  mul := B.totalMul
  one := B.totalOne
  one_mul := B.totalOne_mul
  mul_one := B.totalMul_one
  mul_assoc := B.totalMul_assoc
  left_distrib := B.totalMul_add
  right_distrib := B.totalAdd_mul
  zero_mul := by intro x; funext i l; change B.totalMul 0 x i l=0; simp [totalMul]
  mul_zero := by intro x; funext i l; change B.totalMul x 0 i l=0; simp [totalMul]
  npow := npowRec

noncomputable instance totalAlgebra : Algebra k B.Total :=
  Algebra.ofModule (fun a x y => by
    funext i l
    change B.totalMul (a • x) y i l=(a • B.totalMul x y) i l
    simp [totalMul,map_smul,LinearMap.smul_apply,Finset.smul_sum])
      (fun a x y => by
        funext i l
        change B.totalMul x (a • y) i l=(a • B.totalMul x y) i l
        simp [totalMul,map_smul,Finset.smul_sum])

end LinearComponentAlgebra
end ASGinzburg
