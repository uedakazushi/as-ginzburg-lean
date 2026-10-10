import work.ASGinzburgDraft.BalancedTensorBifunctor
import ASGinzburg.BalancedTensorProjectiveExactness
import work.ASGinzburgDraft.BifunctorTotalRightResolutionAugmentation
import ASGinzburg.BalancedTensorTorLeft
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! The actual double projective resolution for balanced tensor computes
ordinary first-factor Tor. Projectivity supplies exactness of every row. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Category HomologicalComplex
open scoped ModuleCat.Algebra
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable {M : ModuleCat.{max v w} Rᵐᵒᵖ} {N : ModuleCat.{max v w} R}
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)

instance balancedTensorDoubleResolutionRowPreservesHomology (i : ℕ) :
    ((balancedTensorBifunctor.{u,v,max v w,max v w} k R).obj
      (P.complex.X i)).PreservesHomology := by
  letI := P.projective i
  letI : Module.Projective Rᵐᵒᵖ (P.complex.X i) := inferInstance
  exact balancedTensorRightFunctorPreservesHomology k R (P.complex.X i)

instance balancedTensorDoubleResolutionRowPreservesEpimorphisms (i : ℕ) :
    ((balancedTensorBifunctor.{u,v,max v w,max v w} k R).obj
      (P.complex.X i)).PreservesEpimorphisms := by
  change (balancedTensorRightFunctor.{u,v,max v w,max v w} k R
    (P.complex.X i)).PreservesEpimorphisms
  infer_instance

noncomputable def balancedTensorDoubleResolutionAugmentation :
    mapBifunctor P.complex Q.complex (balancedTensorBifunctor k R)
        (ComplexShape.down ℕ) ⟶
      ((balancedTensorLeftFunctor.{u,v,max v w,max v w} k R N).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex :=
  bifunctorTotalRightResolutionAugmentation (balancedTensorBifunctor k R) P.complex Q

instance balancedTensorDoubleResolutionAugmentation_quasiIso :
    QuasiIso (balancedTensorDoubleResolutionAugmentation k R P Q) := by
  letI : ∀ i, ((balancedTensorBifunctor.{u,v,max v w,max v w} k R).obj
    (P.complex.X i)).PreservesHomology :=
    fun i => balancedTensorDoubleResolutionRowPreservesHomology k R P i
  letI : ∀ i, ((balancedTensorBifunctor.{u,v,max v w,max v w} k R).obj
    (P.complex.X i)).PreservesEpimorphisms :=
    fun i => balancedTensorDoubleResolutionRowPreservesEpimorphisms k R P i
  exact bifunctorTotalRightResolutionAugmentation_quasiIso
    (balancedTensorBifunctor k R) P.complex Q

noncomputable def balancedTensorDoubleResolutionHomologyIso (n : ℕ) :
    (mapBifunctor P.complex Q.complex (balancedTensorBifunctor k R)
      (ComplexShape.down ℕ)).homology n ≅
      (((balancedTensorLeftFunctor.{u,v,max v w,max v w} k R N).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homology n :=
  asIso (homologyMap (balancedTensorDoubleResolutionAugmentation k R P Q) n)

noncomputable def balancedTensorDoubleResolutionTorLeftIso (n : ℕ) :
    (mapBifunctor P.complex Q.complex (balancedTensorBifunctor k R)
      (ComplexShape.down ℕ)).homology n ≅
      (balancedTensorTorLeftFunctor.{u,v,max v w,w} k R N n).obj M :=
  balancedTensorDoubleResolutionHomologyIso k R P Q n ≪≫
    (balancedTensorTorLeftResolutionIso.{u,v,max v w,w} k R N M P n).symm

end ASGinzburg
