import ASGinzburg.OppositeJacobianSimpleModules
import ASGinzburg.GinzburgOppositeMinimalResolution
import ASGinzburg.EquivalenceProjectiveResolution
import ASGinzburg.ProjectiveResolutionTargetIso
import ASGinzburg.GinzburgASProjectiveResolution

/-! Original Ginzburg regularity yields genuine projective resolutions
of the original left simple quotients through the proved opposite
regularity, category equivalence and actual simple-module isomorphism. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def GinzburgRegular.leftSimpleProjectiveResolution {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (i : ℤ) :
    ProjectiveResolution ((Q.unrolledJacobianZAlgebra k φ).simpleLeftModule i) := by
  letI : (Q.oppositeJacobianLeftRightEquivalence k φ).symm.functor.Additive := by
    change (Q.oppositeJacobianLeftRightEquivalence k φ).inverse.Additive
    infer_instance
  let j := (Q.vertices : ℤ)-1-i
  let v := Q.opposite.heightEquiv.symm j
  let B := Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)
  have hv : Q.opposite.height v = j := by
    rw [← Q.opposite.heightEquiv_apply]
    exact Q.opposite.heightEquiv.apply_symm_apply j
  let P : ProjectiveResolution (B.simpleRightModule j) :=
    projectiveResolutionTargetIso
      (GinzburgRegular.simpleProjectiveResolution Q.opposite k (h.opposite Q k) v)
      (eqToIso (congrArg B.simpleRightModule hv))
  exact projectiveResolutionTargetIso
    (equivalenceProjectiveResolution (Q.oppositeJacobianLeftRightEquivalence k φ).symm P)
    (Q.oppositeJacobianRightSimpleInverseIso k φ i)

theorem GinzburgRegular.leftSimpleProjectiveResolution_isZero_ge_four {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (i : ℤ) (n : ℕ) :
    IsZero ((h.leftSimpleProjectiveResolution Q k i).complex.X (n+4)) := by
  change IsZero ((Q.oppositeJacobianLeftRightEquivalence k φ).inverse.obj
    ((GinzburgRegular.simpleProjectiveResolution Q.opposite k (h.opposite Q k)
      (Q.opposite.heightEquiv.symm ((Q.vertices : ℤ)-1-i))).complex.X (n+4)))
  exact (Q.oppositeJacobianLeftRightEquivalence k φ).inverse.map_isZero
    (GinzburgRegular.simpleProjectiveResolution_isZero_ge_four Q.opposite k (h.opposite Q k) _ n)

end ASGinzburg.CutQuiver
