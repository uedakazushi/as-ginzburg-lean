import ASGinzburg.GinzburgLeftSimpleProjectiveResolution
import ASGinzburg.OppositeJacobianFiniteProjectives
import ASGinzburg.GinzburgSimpleFiniteProjectiveResolution

/-! Every term of the actual left simple resolution is finitely generated
projective, using actual finite sums and retracts under the equivalence. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem GinzburgRegular.leftSimpleProjectiveResolution_finite {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (i : ℤ) (n : ℕ) :
    (Q.unrolledJacobianZAlgebra k φ).leftFiniteProjectiveProperty
      ((h.leftSimpleProjectiveResolution Q k i).complex.X n) := by
  change (Q.unrolledJacobianZAlgebra k φ).leftFiniteProjectiveProperty
    ((Q.oppositeJacobianLeftRightEquivalence k φ).inverse.obj
      ((GinzburgRegular.simpleProjectiveResolution Q.opposite k (h.opposite Q k)
        (Q.opposite.heightEquiv.symm ((Q.vertices : ℤ)-1-i))).complex.X n))
  exact Q.oppositeJacobianRightFiniteProjective k φ
    (GinzburgRegular.simpleProjectiveResolution_finite Q.opposite k (h.opposite Q k) _ n)

theorem GinzburgRegular.simple_hasLeftFiniteProjectiveResolutionLength {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (i : ℤ) :
    (Q.unrolledJacobianZAlgebra k φ).HasLeftFiniteProjectiveResolutionLength 3
      ((Q.unrolledJacobianZAlgebra k φ).simpleLeftModule i) :=
  (Q.unrolledJacobianZAlgebra k φ).hasLeftFiniteProjectiveResolutionLength_of_fourTermResolution
    (h.leftSimpleProjectiveResolution Q k i)
    (h.leftSimpleProjectiveResolution_isZero_ge_four Q k i 0)
    (fun n _ => h.leftSimpleProjectiveResolution_finite Q k i n)

end ASGinzburg.CutQuiver
