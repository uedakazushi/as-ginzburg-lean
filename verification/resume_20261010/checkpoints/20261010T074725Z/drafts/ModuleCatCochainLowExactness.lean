import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! Low cochain exactness gives the actual first monomorphism and
the two genuine short complexes used in a four-term argument. -/
namespace ASGinzburg
open CategoryTheory
universe u v
variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat.{v} R) ℕ)

theorem cochain_first_d_mono_of_exactAt_zero (h : K.ExactAt 0) :
    Mono (K.d 0 1) := by
  have he := (K.exactAt_iff' 0 0 1 (by simp) (by simp)).mp h
  exact ((K.sc' 0 0 1).exact_iff_mono (K.shape 0 0 (by simp))).mp he

theorem cochain_low_shortComplex_exact (n : ℕ) (h : K.ExactAt (n+1)) :
    (ShortComplex.mk (K.d n (n+1)) (K.d (n+1) (n+2))
      (K.d_comp_d n (n+1) (n+2))).Exact := by
  exact (K.exactAt_iff' n (n+1) (n+2) (by simp) (by simp)).mp h

end ASGinzburg
