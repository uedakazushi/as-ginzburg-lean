import ASGinzburg.ASCutSemisimpleTorFinite
import ASGinzburg.BalancedTensorLeftFieldModuleChange

/-! The actual bundled AS left semisimple quotient and the raw quotient
give naturally isomorphic balanced tensor functors over the field. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

set_option maxHeartbeats 1000000 in
noncomputable def ASRegular.cutSemisimpleLeftTensorRawFieldIso (hAS : A.ASRegular Q) :
    balancedTensorLeftFunctor.{u,v,v,v} k (hAS.CutGradedAlgebra A Q)
        (hAS.cutSemisimpleLeftObject A Q) ≅
      balancedTensorLeftFunctor.{u,v,v,v} k (hAS.CutGradedAlgebra A Q)
        (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q) := by
  let R := hAS.CutGradedAlgebra A Q
  let J := hAS.cutGradedRadical A Q
  exact balancedTensorLeftFunctorFieldModuleChangeIso k R (R ⧸ J)
    (Module.compHom (R ⧸ J) (algebraMap k R))
    (inferInstance : Module k (R ⧸ J))
    (algebraModuleCompHomField_eq k R (R ⧸ J))

end ASGinzburg.ZAlgebra
