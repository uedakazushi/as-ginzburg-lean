import ASGinzburg.ASCutSemisimpleRightSharpDimension
import ASGinzburg.ASCutRegularEnvelopingDimensionLowerBound

/-! Every cut quiver has at least three vertices by its original
invariant. Thus its actual AS radical quotient has projective dimension
three, and its actual regular enveloping module has projective dimension
at least three, without a separate vertex existence assumption. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutSemisimpleRight_projectiveDimension_eq_three_unconditional
    (hAS : A.ASRegular Q) :
    projectiveDimension (hAS.cutSemisimpleRightObject A Q) = 3 := by
  let i : Q.Vertex := ⟨0,by have h := Q.at_least_three; omega⟩
  letI : Nonempty Q.Vertex := ⟨i⟩
  exact hAS.cutSemisimpleRight_projectiveDimension_eq_three A Q

theorem ASRegular.cutRegularEnveloping_projectiveDimension_ge_three_unconditional
    (hAS : A.ASRegular Q) :
    (3 : WithBot ℕ∞) ≤
      projectiveDimension (regularEnvelopingModuleCat k (hAS.CutGradedAlgebra A Q)) := by
  let i : Q.Vertex := ⟨0,by have h := Q.at_least_three; omega⟩
  exact hAS.cutRegularEnveloping_projectiveDimension_ge_three A Q (i,0)

end ASGinzburg.ZAlgebra
