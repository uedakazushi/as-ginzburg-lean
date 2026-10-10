import ASGinzburg.BalancedTensorFinite
import ASGinzburg.BalancedTensorTorLeft
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Finiteness of the genuine derived balanced tensor follows from
the finite term of an actual projective resolution, without a ring
finiteness assumption. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v w z

theorem moduleCatShortComplexHomology_finite
    (k : Type u) [Field k] (S : ShortComplex (ModuleCat.{v} k))
    [Module.Finite k S.X₂] : Module.Finite k S.homology := by
  haveI : Module.Finite k S.moduleCatLeftHomologyData.H := by
    change Module.Finite k (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm

open scoped ModuleCat.Algebra

variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (N : Type w) [AddCommGroup N] [Module k N] [Module R N]

theorem balancedTensorTorLeft_finite_of_resolution_term
    (M : ModuleCat.{max v w z} Rᵐᵒᵖ) (P : ProjectiveResolution M) (n : ℕ)
    [Module.Finite Rᵐᵒᵖ (P.complex.X n)] [Module.Finite k N] :
    Module.Finite k ((balancedTensorTorLeftFunctor.{u,v,w,z} k R N n).obj M) := by
  let F := balancedTensorLeftFunctor.{u,v,w,max v w z} k R N
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  haveI : Module.Finite k (K.X n) :=
    balancedTensorSpace_finite k R (P.complex.X n) N
  haveI : Module.Finite k (K.sc n).X₂ := by
    change Module.Finite k (K.X n)
    infer_instance
  haveI : Module.Finite k (K.homology n) :=
    moduleCatShortComplexHomology_finite k (K.sc n)
  haveI : Module.Finite k
      ((HomologicalComplex.homologyFunctor (ModuleCat.{max v w z} k)
        (ComplexShape.down ℕ) n).obj
        (((balancedTensorLeftFunctor.{u,v,w,max v w z} k R N).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex)) := by
    change Module.Finite k (K.homology n)
    infer_instance
  exact Module.Finite.equiv (balancedTensorTorLeftResolutionIso k R N M P n).toLinearEquiv.symm

end ASGinzburg
