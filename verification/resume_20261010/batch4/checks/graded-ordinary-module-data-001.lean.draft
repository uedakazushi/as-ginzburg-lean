import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Category.ModuleCat.Algebra

/-! Genuine graded data on ordinary ring modules, retaining the actual
module category object and its canonical scalar action. Concrete kernels
and covers can use this data without a new category of graded modules. -/
namespace ASGinzburg
open CategoryTheory
open scoped DirectSum ModuleCat.Algebra
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (A : ℤ → Submodule k R)

structure GradedOrdinaryModuleData where
  ringModule : ModuleCat.{v} R
  grade : ℤ → Submodule k ringModule
  isInternal : DirectSum.IsInternal grade
  smul_mem : ∀ p q : ℤ, ∀ r ∈ A p, ∀ x ∈ grade q, r • x ∈ grade (p + q)

namespace GradedOrdinaryModuleData
variable {k R A}
variable (M : GradedOrdinaryModuleData k R A)

noncomputable def decomposition : DirectSum.Decomposition M.grade :=
  M.isInternal.chooseDecomposition

def BoundedBelow (b : ℤ) : Prop :=
  ∀ q : ℤ, q < b → M.grade q = ⊥

def PreservesGrade (N : GradedOrdinaryModuleData k R A) (f : M.ringModule ⟶ N.ringModule) : Prop :=
  ∀ q : ℤ, ∀ x : M.ringModule, x ∈ M.grade q → f x ∈ N.grade q

theorem preservesGrade_id : M.PreservesGrade M (𝟙 M.ringModule) :=
  fun _ _ hx => hx

theorem preservesGrade_comp (N P : GradedOrdinaryModuleData k R A)
    (f : M.ringModule ⟶ N.ringModule) (g : N.ringModule ⟶ P.ringModule)
    (hf : M.PreservesGrade N f) (hg : N.PreservesGrade P g) :
    M.PreservesGrade P (f ≫ g) :=
  fun q x hx => hg q (f x) (hf q x hx)

end GradedOrdinaryModuleData
end ASGinzburg
