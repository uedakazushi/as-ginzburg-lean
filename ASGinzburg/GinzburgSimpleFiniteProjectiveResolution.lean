import ASGinzburg.GinzburgASProjectiveResolution
import ASGinzburg.FiniteProjectiveResolutionLength

/-! Every term of the actual Ginzburg simple resolution is finitely
generated projective. Actual finite covers of length three are derived
without imposing minimality or any AS/Ext hypothesis. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgASProjectiveComplexTerm_finite (φ : Q.Potential k)
    (v : Q.LiftVertex) (n : ℕ) :
    (Q.unrolledJacobianZAlgebra k φ).rightFiniteProjectiveProperty
      (Q.ginzburgASProjectiveComplexTerm k φ v n) := by
  let A := Q.unrolledJacobianZAlgebra k φ
  rcases n with _|_|_|_|n
  · exact A.rightFiniteProjectiveProperty_representable _
  · dsimp [ginzburgASProjectiveComplexTerm,ZAlgebra.asResolutionTerm₁]
    exact A.rightFiniteProjectiveProperty_coproduct _
  · dsimp [ginzburgASProjectiveComplexTerm,ZAlgebra.asResolutionTerm₂]
    exact A.rightFiniteProjectiveProperty_coproduct _
  · exact A.rightFiniteProjectiveProperty_representable _
  · exact A.rightFiniteProjectiveProperty_of_isZero (isZero_zero _)

theorem GinzburgRegular.simpleProjectiveResolution_finite {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) (n : ℕ) :
    (Q.unrolledJacobianZAlgebra k φ).rightFiniteProjectiveProperty
      ((h.simpleProjectiveResolution Q k v).complex.X n) :=
  Q.ginzburgASProjectiveComplexTerm_finite k φ v n

theorem GinzburgRegular.simple_hasRightFiniteProjectiveResolutionLength {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) :
    (Q.unrolledJacobianZAlgebra k φ).HasRightFiniteProjectiveResolutionLength 3
      ((Q.unrolledJacobianZAlgebra k φ).simpleRightModule (Q.height v)) :=
  (Q.unrolledJacobianZAlgebra k φ).hasRightFiniteProjectiveResolutionLength_of_fourTermResolution
    (h.simpleProjectiveResolution Q k v)
    (h.simpleProjectiveResolution_isZero_ge_four Q k v 0)
    (fun n _ => h.simpleProjectiveResolution_finite Q k v n)

end ASGinzburg.CutQuiver
