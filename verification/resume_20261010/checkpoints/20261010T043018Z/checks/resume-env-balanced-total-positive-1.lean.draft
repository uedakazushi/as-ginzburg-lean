import work.ASGinzburgDraft.BalancedTensorBifunctor
import work.ASGinzburgDraft.BalancedTensorProjectiveExactness
import work.ASGinzburgDraft.BicomplexTotalBoundedRows
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-! Actual projective right factors make the positive vertical rows of
the balanced tensor double resolution exact. A bounded first resolution
therefore bounds the genuine total homology. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ModuleCat.Algebra
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable {M : ModuleCat.{max v w} Rᵐᵒᵖ} {N : ModuleCat.{max v w} R}
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)

theorem balancedTensorResolutionRow_exactAt (i j : ℕ) (hj : 0 < j) :
    ((((balancedTensorBifunctor k R).obj (P.complex.X i)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj Q.complex).ExactAt j := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  letI := P.projective i
  letI : Module.Projective Rᵐᵒᵖ (P.complex.X i) := inferInstance
  exact (Q.complex_exactAt_succ s).map (balancedTensorRightFunctor k R (P.complex.X i))

theorem balancedTensorTotal_exactAt_of_bounded_resolution
    (a n : ℕ) (hn : a < n)
    (hP : ∀ i, a < i → IsZero (P.complex.X i)) :
    (mapBifunctor P.complex Q.complex (balancedTensorBifunctor k R)
      (ComplexShape.down ℕ)).ExactAt n :=
  bifunctorTotal_exactAt_of_bounded_left (balancedTensorBifunctor k R)
    P.complex Q.complex a n hn hP
    (fun i j _ hj => balancedTensorResolutionRow_exactAt k R P Q i j hj)

theorem balancedTensorTotal_isZero_homology_of_bounded_resolution
    (a n : ℕ) (hn : a < n)
    (hP : ∀ i, a < i → IsZero (P.complex.X i)) :
    IsZero ((mapBifunctor P.complex Q.complex (balancedTensorBifunctor k R)
      (ComplexShape.down ℕ)).homology n) :=
  (balancedTensorTotal_exactAt_of_bounded_resolution k R P Q a n hn hP).isZero_homology

end ASGinzburg
