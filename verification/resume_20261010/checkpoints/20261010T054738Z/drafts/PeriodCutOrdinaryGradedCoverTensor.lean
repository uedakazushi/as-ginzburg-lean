import work.ASGinzburgDraft.PeriodCutOrdinaryGradedCover
import work.ASGinzburgDraft.BalancedTensorMinimalCoverIso

/-! The constructed native graded projective cover becomes an actual
isomorphism after tensoring with the semisimple radical quotient. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))
local notation "R" => E.CutGradedRing (fun i : Q.Vertex => (Fin.val i : ℤ))

theorem cutOrdinaryGradedCoverπ_kernel_tensorIdealAction
    (M : GradedOrdinaryModuleData k Rᵐᵒᵖ (E.cutIntegerOppositeHomogeneousSpace Q))
    (x : (E.cutOrdinaryGradedCoverSource Q M).ringModule)
    (hx : E.cutOrdinaryGradedCoverπ Q M x = 0) :
    x ∈ balancedTensorIdealAction k R
      (E.cutOrdinaryGradedCoverSource Q M).ringModule (E.cutGradedJacobson Q) := by
  have h := E.cutOrdinaryGradedCoverπ_kernel_minimal Q M x hx
  apply Submodule.span_mono _ h
  rintro a ⟨r, hr, m, hm⟩
  exact ⟨(⟨r.unop, (E.cutGradedJacobsonOppositeIdeal_mem Q r).mp hr⟩, m),
    by simpa only [MulOpposite.op_unop] using hm⟩

theorem cutOrdinaryGradedCoverπ_tensor_semisimple_isIso
    (b : ℤ) (M : GradedOrdinaryModuleData k Rᵐᵒᵖ (E.cutIntegerOppositeHomogeneousSpace Q))
    (hb : M.BoundedBelow b) :
    IsIso ((balancedTensorLeftFunctor k R (R ⧸ E.cutGradedJacobson Q)).map
      (E.cutOrdinaryGradedCoverπ Q M)) := by
  letI := E.cutOrdinaryGradedCoverπ_epi Q M b hb
  exact balancedTensorLeftFunctor_map_isIso_of_minimal_epi k R (E.cutGradedJacobson Q)
    (E.cutOrdinaryGradedCoverπ Q M) (E.cutOrdinaryGradedCoverπ_kernel_tensorIdealAction Q M)

theorem cutOrdinaryGradedProjectiveCover_tensor_semisimple_isIso
    (b : ℤ) (M : GradedOrdinaryModuleData k Rᵐᵒᵖ (E.cutIntegerOppositeHomogeneousSpace Q))
    (hb : M.BoundedBelow b) :
    IsIso ((balancedTensorLeftFunctor k R (R ⧸ E.cutGradedJacobson Q)).map
      (E.cutOrdinaryGradedProjectiveCover Q b M hb).π) :=
  E.cutOrdinaryGradedCoverπ_tensor_semisimple_isIso Q b M hb

end ASGinzburg.ZAlgebra.PeriodIso
