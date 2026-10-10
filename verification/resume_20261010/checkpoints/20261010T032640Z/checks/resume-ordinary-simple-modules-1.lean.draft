import work.ASGinzburgDraft.ASCutOrdinaryResolutions
import ASGinzburg.PeriodCutGradedSimpleSpaces
import Mathlib.Algebra.Category.ModuleCat.Simple

/-! The forgotten cover vertex modules are actual simple objects of
ordinary right-R ModuleCat, because their genuine k-total spaces have
dimension one. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutOrdinarySimple_space_finrank (hAS : A.ASRegular Q)
    (x : Q.LiftVertex) : Module.finrank k (hAS.cutGradedSimple A Q x).space=1 :=
  (hAS.periodIso A Q).cornerSimpleTotalSpace_finrank Q x

instance ASRegular.cutOrdinarySimple_simple (hAS : A.ASRegular Q)
    (x : Q.LiftVertex) : Simple (hAS.cutOrdinarySimple A Q x) := by
  change Simple (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ
    (hAS.cutGradedSimple A Q x).space)
  apply simple_iff_isSimpleModule.mpr
  apply (isSimpleModule_iff ..).mpr
  exact is_simple_module_of_finrank_eq_one (hAS.cutOrdinarySimple_space_finrank A Q x)

end ASGinzburg.ZAlgebra
