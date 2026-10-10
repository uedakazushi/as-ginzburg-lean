import ASGinzburg.EnvelopingResolutionRightProjectiveDimension
import ASGinzburg.ProjectiveDimensionTwoDerivedVanishing
import ASGinzburg.ASCutOrdinarySimpleSharpDimension

/-! The original AS condition forces the actual multiplication bimodule
to have projective dimension at least three. A shorter bimodule resolution
would give a shorter ordinary vertex resolution and kill its actual third Tor. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutRegularEnveloping_projectiveDimension_ge_three
    (hAS : A.ASRegular Q) (x : Q.LiftVertex) :
    (3 : WithBot ℕ∞) ≤
      projectiveDimension (regularEnvelopingModuleCat k (hAS.CutGradedAlgebra A Q)) := by
  apply (projectiveDimension_ge_iff _ 3).mpr
  intro hR
  let R := hAS.CutGradedAlgebra A Q
  let P := projectiveDimensionTwoResolution
    (CategoryTheory.projectiveResolution (regularEnvelopingModuleCat k R)) hR
  let U := envelopingResolutionRightProjectiveResolution k R
    (hAS.cutOrdinarySimple A Q x) P
  have h₃ : IsZero (U.complex.X 3) :=
    envelopingResolutionRightProjectiveResolution_isZero k R
      (hAS.cutOrdinarySimple A Q x) P 3
      (projectiveDimensionTwoResolution_isZero_ge_three
        (CategoryTheory.projectiveResolution (regularEnvelopingModuleCat k R)) hR 0)
  exact hAS.cutOrdinarySimpleTorRadicalQuotient_three_not_isZero A Q x
    (balancedTensorTorLeft_isZero_of_resolution_term k R
      (R ⧸ hAS.cutGradedRadical A Q) (hAS.cutOrdinarySimple A Q x) U 3 h₃)

end ASGinzburg.ZAlgebra
