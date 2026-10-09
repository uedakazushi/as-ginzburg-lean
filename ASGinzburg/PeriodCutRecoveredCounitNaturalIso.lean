import ASGinzburg.PeriodCutRecoveredGradedModuleIso
import ASGinzburg.PeriodCutRecoveredModuleFunctor
import ASGinzburg.PeriodCutGradedFunctorLinear

/-! The recovered-to-original graded R-module isomorphism is natural. -/
namespace ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
open CategoryTheory
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

noncomputable def recoveredCounitNaturalIso :
    recoveredModuleFunctor (E:=E) ⋙ E.cornerGradedModuleFunctor Q ≅
      𝟭 (E.CutGradedRightModule Q) :=
  NatIso.ofComponents (fun M => M.recoveredGradedModuleIso) (by
    intro M N f
    apply Subtype.ext
    apply DFinsupp.lhom_ext
    intro x v
    change N.recoveredTotalEquiv
      (E.cornerTotalModuleLinearMap Q (recoveredModuleMap f)
        (DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M.recoveredRightModule) x v))=
      f.val (M.recoveredTotalEquiv
        (DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M.recoveredRightModule) x v))
    rw [E.cornerTotalModuleLinearMap_lof,N.recoveredTotalEquiv_lof,M.recoveredTotalEquiv_lof,
      N.recoveredCoordinateSpaceEquiv_val,M.recoveredCoordinateSpaceEquiv_val]
    rfl)

end ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
