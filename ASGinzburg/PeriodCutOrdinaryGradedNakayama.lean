import ASGinzburg.GradedOrdinaryModuleData
import ASGinzburg.PeriodCutIntegerHomogeneousSpaces
import ASGinzburg.PeriodCutGradedTensorNakayama
import Mathlib.Algebra.Algebra.Opposite

/-! Genuine graded data on an ordinary right module over the native cut
ring gives the native graded right module. The actual semisimple tensor
functor therefore detects its zero object from its actual lower bound. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cutIntegerOppositeHomogeneousSpace (q : ℤ) :
    Submodule k (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))ᵐᵒᵖ :=
  (E.cutIntegerHomogeneousSpace Q q).map (MulOpposite.opLinearEquiv k).toLinearMap

theorem cutIntegerOppositeHomogeneousSpace_op_mem (q : ℤ)
    (r : E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))
    (hr : r ∈ E.cutIntegerHomogeneousSpace Q q) :
    MulOpposite.op r ∈ E.cutIntegerOppositeHomogeneousSpace Q q := ⟨r,hr,rfl⟩

variable (M : GradedOrdinaryModuleData k
  (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))ᵐᵒᵖ
  (E.cutIntegerOppositeHomogeneousSpace Q))

noncomputable def ordinaryGradedDataCutRightModule : E.CutGradedRightModule Q where
  space := ModuleCat.of k M.ringModule
  representation := (AlgHom.op (Algebra.lsmul k k M.ringModule)).comp
    (AlgEquiv.opOp k (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))).toAlgHom
  grade := M.grade
  decomposition := M.decomposition
  homogeneous := by
    intro m r q x hx
    change MulOpposite.op (E.cutHomogeneousInclusion (fun i : Q.Vertex => (i.val:ℤ)) m r) • x ∈ _
    have hr : E.cutHomogeneousInclusion (fun i : Q.Vertex => (i.val:ℤ)) m r ∈
        E.cutIntegerHomogeneousSpace Q (m:ℤ) := by
      rw [E.cutIntegerHomogeneousSpace_ofNat]
      exact ⟨r,rfl⟩
    simpa only [add_comm] using M.smul_mem (m:ℤ) q _
      (E.cutIntegerOppositeHomogeneousSpace_op_mem Q (m:ℤ) _ hr) x hx

noncomputable def ordinaryGradedDataCutRightModuleIso :
    (E.ordinaryGradedDataCutRightModule Q M).ringModule ≅ M.ringModule :=
  LinearEquiv.toModuleIso {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
  }

theorem ordinaryGradedData_isZero_of_tensor_semisimple
    (b : ℤ) (hb : M.BoundedBelow b)
    (hT : IsZero ((balancedTensorLeftFunctor k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q)).obj
      M.ringModule)) : IsZero M.ringModule := by
  have hNative : IsZero ((balancedTensorLeftFunctor k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q)).obj
      (E.ordinaryGradedDataCutRightModule Q M).ringModule) :=
    ((balancedTensorLeftFunctor k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q)).mapIso
      (E.ordinaryGradedDataCutRightModuleIso Q M)).isZero_iff.mpr hT
  have hZero := (E.ordinaryGradedDataCutRightModule Q M).ringModule_isZero_of_grade_lower_bound_tensor_functor b hb hNative
  exact (E.ordinaryGradedDataCutRightModuleIso Q M).isZero_iff.mp hZero

end ASGinzburg.ZAlgebra.PeriodIso
