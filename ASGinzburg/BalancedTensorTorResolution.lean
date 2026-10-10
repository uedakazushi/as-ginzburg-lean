import ASGinzburg.BalancedTensorTor

/-! Genuine computations of balanced Tor from a chosen projective
resolution: vanishing in a zero term and identification with the tensor
of a resolution term when both adjacent tensor differentials vanish. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]

theorem balancedTensorTor_isZero_of_resolution_term
    (N : ModuleCat.{max v w z} R) (Q : ProjectiveResolution N) (n : ℕ)
    (h : IsZero (Q.complex.X n)) :
    IsZero ((balancedTensorTorFunctor.{u,v,w,z} k R M n).obj N) := by
  let F := balancedTensorRightFunctor.{u,v,w,max v w z} k R M
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  have hK : IsZero (K.homology n) :=
    (K.sc n).isZero_homology_of_isZero_X₂ (F.map_isZero h)
  exact IsZero.of_iso hK (balancedTensorTorResolutionIso k R M N Q n)

noncomputable def balancedTensorTorZeroDifferentialsIso
    (N : ModuleCat.{max v w z} R) (Q : ProjectiveResolution N) (n : ℕ)
    (hin : (balancedTensorRightFunctor.{u,v,w,max v w z} k R M).map
      (Q.complex.d ((ComplexShape.down ℕ).prev n) n) = 0)
    (hout : (balancedTensorRightFunctor.{u,v,w,max v w z} k R M).map
      (Q.complex.d n ((ComplexShape.down ℕ).next n)) = 0) :
    (balancedTensorTorFunctor.{u,v,w,z} k R M n).obj N ≅
      (balancedTensorRightFunctor.{u,v,w,max v w z} k R M).obj (Q.complex.X n) := by
  let F := balancedTensorRightFunctor.{u,v,w,max v w z} k R M
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  exact balancedTensorTorResolutionIso k R M N Q n ≪≫
    (ShortComplex.HomologyData.ofZeros (K.sc n) hin hout).left.homologyIso

end ASGinzburg
