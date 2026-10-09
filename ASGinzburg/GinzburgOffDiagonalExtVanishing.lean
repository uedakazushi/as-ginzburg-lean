import ASGinzburg.GinzburgOffDiagonalHomSurjectivity
import ASGinzburg.ProjectiveResolutionTopExtVanishing
import ASGinzburg.GinzburgASProjectiveResolution
import ASGinzburg.GinzburgMinimalASResolution

/-! Actual degree-three Ext vanishes away from the required previous
sheet, proved from native opposite exactness and genuine syzygies. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k] (φ : Q.Potential k)

theorem ginzburgASHom_lift_three_off_diagonal
    (v l : Q.LiftVertex) (hne : l≠Q.tau.symm v)
    (f : (Q.unrolledJacobianZAlgebra k φ).representable (Q.height (Q.tau.symm v)) ⟶
      (Q.unrolledJacobianZAlgebra k φ).representable (Q.height l)) :
    ∃ g : (Q.unrolledJacobianZAlgebra k φ).asResolutionTerm₂ Q v ⟶
      (Q.unrolledJacobianZAlgebra k φ).representable (Q.height l),
      Q.ginzburgASProjectiveD₃ k φ v ≫ g=f := by
  let e₂ := (Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorDualTermIso Q v
  let e₃ := (Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorLoopTermIso Q v
  obtain ⟨g,hg⟩ := Q.ginzburgNativeHom_lift_three_off_diagonal k φ v l hne (e₃.hom ≫ f)
  refine ⟨e₂.inv ≫ g,?_⟩
  calc
    _ = e₃.inv ≫ (Q.ginzburgLoopDualProjectiveMap k φ v ≫ g) := by
      simp [ginzburgASProjectiveD₃,e₂,e₃,Category.assoc]
    _ = e₃.inv ≫ (e₃.hom ≫ f) := by rw [hg]
    _ = f := by simp

theorem GinzburgRegular.simpleExt_three_off_diagonal_eq_zero
    (h : Q.GinzburgRegular k φ) (v l : Q.LiftVertex) (hne : l≠Q.tau.symm v)
    (e : Abelian.Ext.{u}
      ((Q.unrolledJacobianZAlgebra k φ).simpleRightModule (Q.height v))
      ((Q.unrolledJacobianZAlgebra k φ).representable (Q.height l)) 3) : e=0 := by
  apply (h.simpleProjectiveResolution Q k v).ext_three_eq_zero_of_hom_surjective
    (h.simpleProjectiveResolution_isZero_ge_four Q k v 0)
    ((Q.unrolledJacobianZAlgebra k φ).representable (Q.height l)) _ e
  intro f
  obtain ⟨g,hg⟩ := Q.ginzburgASHom_lift_three_off_diagonal k φ v l hne f
  refine ⟨g,?_⟩
  change (Q.ginzburgASProjectiveComplex k φ v).d 3 2 ≫ g=f
  rw [Q.ginzburgASProjectiveComplex_d]
  exact hg

end ASGinzburg.CutQuiver
