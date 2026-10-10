import ASGinzburg.ASCutSemisimpleTorFinite
import ASGinzburg.IdealQuotientRightFieldComparison

/-! The original AS quotient coordinates make the actual bundled right
semisimple module finite over its canonical field action. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutSemisimpleRightObject_fieldFinite (hAS : A.ASRegular Q) :
    Module.Finite k (hAS.cutSemisimpleRightObject A Q) := by
  let R := hAS.CutGradedAlgebra A Q
  let J := hAS.cutGradedRadical A Q
  letI : Module.Finite k (R ⧸ J) :=
    Module.Finite.equiv (hAS.cutGradedRadicalQuotientAlgEquiv A Q).symm.toLinearEquiv
  letI : Module.Finite k (R ⧸ J)ᵐᵒᵖ :=
    Module.Finite.equiv (MulOpposite.opLinearEquiv k : (R ⧸ J) ≃ₗ[k] (R ⧸ J)ᵐᵒᵖ)
  exact Module.Finite.equiv (idealQuotientRightCanonicalFieldIso k R J).toLinearEquiv.symm

end ASGinzburg.ZAlgebra
