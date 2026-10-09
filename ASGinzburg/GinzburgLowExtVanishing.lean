import ASGinzburg.GinzburgASHomExactness
import ASGinzburg.GinzburgASProjectiveResolution
import ASGinzburg.ProjectiveResolutionHomComplex

/-! Genuine negative Ginzburg homology vanishing implies vanishing
of the actual derived-category Ext in degrees zero, one, and two. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k] (φ : Q.Potential k)

theorem GinzburgRegular.simpleProjectiveResolution_homComplex_exactAt_low
    (h : Q.GinzburgRegular k φ) (v l : Q.LiftVertex) (n : ℕ) (hn : n<3) :
    ((h.simpleProjectiveResolution Q k v).homComplex (k := k)
      ((Q.unrolledJacobianZAlgebra k φ).representable (Q.height l))).ExactAt n := by
  rcases n with _|_|_|n
  · rw [ProjectiveResolution.homComplex_exactAt_zero_iff]
    intro f hf
    change (Q.ginzburgASProjectiveComplex k φ v).d 1 0 ≫ f=0 at hf
    rw [Q.ginzburgASProjectiveComplex_d] at hf
    exact h.asHom_zero_kernel Q k φ v l f hf
  · rw [ProjectiveResolution.homComplex_exactAt_succ_iff]
    intro f hf
    change (Q.ginzburgASProjectiveComplex k φ v).d 2 1 ≫ f=0 at hf
    rw [Q.ginzburgASProjectiveComplex_d] at hf
    exact h.asHom_lift_one Q k φ v l f hf
  · rw [ProjectiveResolution.homComplex_exactAt_succ_iff]
    intro f hf
    change (Q.ginzburgASProjectiveComplex k φ v).d 3 2 ≫ f=0 at hf
    rw [Q.ginzburgASProjectiveComplex_d] at hf
    exact Q.ginzburgASHom_lift_two k φ v l f hf
  · omega

theorem GinzburgRegular.simpleExt_low_eq_zero_representable
    (h : Q.GinzburgRegular k φ) (v l : Q.LiftVertex) (n : ℕ) (hn : n<3)
    (e : Abelian.Ext.{u}
      ((Q.unrolledJacobianZAlgebra k φ).simpleRightModule (Q.height v))
      ((Q.unrolledJacobianZAlgebra k φ).representable (Q.height l)) n) : e=0 :=
  (h.simpleProjectiveResolution Q k v).ext_low_eq_zero_of_homComplex_exact
    ((Q.unrolledJacobianZAlgebra k φ).representable (Q.height l)) n hn
    (h.simpleProjectiveResolution_homComplex_exactAt_low Q k φ v l n hn) e

end ASGinzburg.CutQuiver
