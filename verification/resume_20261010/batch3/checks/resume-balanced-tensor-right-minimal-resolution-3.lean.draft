import ASGinzburg.BalancedTensorTorResolution
import ASGinzburg.BalancedTensorRightMaps

/-! Actual second-factor Tor is the tensor of a chosen resolution term
when the left-module differentials lie in an actual ideal action span
annihilating the fixed right module. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v w z z'
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable {N : Type z} [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
variable {N' : Type z'} [AddCommGroup N'] [Module k N'] [Module R N'] [IsScalarTower k R N']

omit [Algebra k R] [IsScalarTower k R N] [IsScalarTower k R N'] in
theorem balancedTensorTmul_eq_zero_of_left_action_span
    (I : Set R) (hM : ∀ r ∈ I, ∀ x : M, MulOpposite.op r • x=0)
    (x : M) {y : N'} (hy : y ∈ Submodule.span k
      {a : N' | ∃ r ∈ I, ∃ n : N', r • n=a}) :
    balancedTensorTmul k R M N' x y=0 := by
  induction hy using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨r,hr,n,rfl⟩ := ha
    rw [← balancedTensorTmul_balance, hM r hr x]
    change (balancedTensorBilinear k R M N' 0) n=0
    rw [map_zero]
    rfl
  | zero => exact (balancedTensorBilinear k R M N' x).map_zero
  | add a b ha hb iha ihb =>
    change (balancedTensorBilinear k R M N' x) a=0 at iha
    change (balancedTensorBilinear k R M N' x) b=0 at ihb
    change (balancedTensorBilinear k R M N' x) (a+b)=0
    rw [map_add,iha,ihb,add_zero]
  | smul c a ha ih =>
    change (balancedTensorBilinear k R M N' x) a=0 at ih
    change (balancedTensorBilinear k R M N' x) (c • a)=0
    rw [map_smul,ih,smul_zero]

theorem balancedTensorMapRight_eq_zero_of_action_span
    (I : Set R) (hM : ∀ r ∈ I, ∀ x : M, MulOpposite.op r • x=0)
    (g : N →ₗ[R] N')
    (hg : ∀ y : N, g y ∈ Submodule.span k
      {a : N' | ∃ r ∈ I, ∃ n : N', r • n=a}) :
    balancedTensorMapRight k R M g=0 := by
  apply balancedTensorSpace_linearMap_ext k R M N
  intro x y
  rw [balancedTensorMapRight_tmul]
  exact balancedTensorTmul_eq_zero_of_left_action_span k R M I hM x (hg y)

theorem balancedTensorRightFunctor_map_eq_zero_of_action_span
    {N N' : ModuleCat.{z} R} (I : Set R)
    (hM : ∀ r ∈ I, ∀ x : M, MulOpposite.op r • x=0)
    (g : N ⟶ N') (hg : ∀ y : N, g y ∈ Submodule.span k
      {a : N' | ∃ r ∈ I, ∃ n : N', r • n=a}) :
    (balancedTensorRightFunctor k R M).map g=0 := by
  apply ModuleCat.hom_ext
  exact balancedTensorMapRight_eq_zero_of_action_span k R M I hM g.hom hg

noncomputable def balancedTensorTorRightMinimalResolutionIso
    (N : ModuleCat.{max v w z} R) (P : ProjectiveResolution N)
    (I : Set R) (hM : ∀ r ∈ I, ∀ x : M, MulOpposite.op r • x=0)
    (hP : ∀ i j, ∀ y : P.complex.X i, P.complex.d i j y ∈ Submodule.span k
      {a : P.complex.X j | ∃ r ∈ I, ∃ n : P.complex.X j, r • n=a})
    (n : ℕ) :
    (balancedTensorTorFunctor.{u,v,w,z} k R M n).obj N ≅
      (balancedTensorRightFunctor.{u,v,w,max v w z} k R M).obj (P.complex.X n) :=
  balancedTensorTorZeroDifferentialsIso k R M N P n
    (balancedTensorRightFunctor_map_eq_zero_of_action_span k R M I hM _ (hP _ _))
    (balancedTensorRightFunctor_map_eq_zero_of_action_span k R M I hM _ (hP _ _))

theorem balancedTensorTorRightMinimalResolution_isZero_iff
    (N : ModuleCat.{max v w z} R) (P : ProjectiveResolution N)
    (I : Set R) (hM : ∀ r ∈ I, ∀ x : M, MulOpposite.op r • x=0)
    (hP : ∀ i j, ∀ y : P.complex.X i, P.complex.d i j y ∈ Submodule.span k
      {a : P.complex.X j | ∃ r ∈ I, ∃ n : P.complex.X j, r • n=a})
    (n : ℕ) :
    IsZero ((balancedTensorTorFunctor.{u,v,w,z} k R M n).obj N) ↔
      IsZero ((balancedTensorRightFunctor.{u,v,w,max v w z} k R M).obj (P.complex.X n)) :=
  (balancedTensorTorRightMinimalResolutionIso k R M N P I hM hP n).isZero_iff

end ASGinzburg
