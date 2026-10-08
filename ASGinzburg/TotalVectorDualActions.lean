import ASGinzburg.TotalVectorDuality
import ASGinzburg.TotalModuleRepresentations

/-! The total vector-dual comparison respects every component and every element
of the actual finite-support total algebra on both sides. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem rightModuleVectorDualTotalLinearMap_component_action (M : A.RightModule)
    {i j : ℤ} (a : A.Hom i j) (φ : A.leftModuleTotalSpace (A.rightModuleVectorDual M)) :
    A.rightModuleVectorDualTotalLinearMap M (A.leftModuleTotalAction (A.rightModuleVectorDual M) a φ) =
      (A.rightModuleVectorDualTotalLinearMap M φ).comp (A.rightModuleTotalAction M a) := by
  apply DirectSum.linearMap_ext
  intro t
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  by_cases ht : t = j
  · subst t
    rw [A.rightModuleTotalAction_lof, A.rightModuleVectorDualTotalLinearMap_eval_lof,
      A.rightModuleVectorDualTotalLinearMap_eval_lof]
    change (A.scalarEndEquiv 0).symm
      (((DirectSum.lof k ℤ (fun l => (A.leftModuleEvaluation l).obj (A.rightModuleVectorDual M)) j
        (((A.rightModuleVectorDual M).obj.map (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a)).hom (φ i))) j).hom x) = _
    rw [DirectSum.lof_apply]
    rfl
  · rw [A.rightModuleTotalAction_lof_off M a t ht, map_zero,
      A.rightModuleVectorDualTotalLinearMap_eval_lof]
    change (A.scalarEndEquiv 0).symm
      (((DFinsupp.single j
        (((A.rightModuleVectorDual M).obj.map (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a)).hom (φ i)) :
          A.leftModuleTotalSpace (A.rightModuleVectorDual M)) t).hom x) = 0
    rw [DFinsupp.single_eq_of_ne ht]
    simp

theorem leftModuleVectorDualTotalLinearMap_component_action (M : A.LeftModule)
    {i j : ℤ} (a : A.Hom i j) (φ : A.rightModuleTotalSpace (A.leftModuleVectorDual M)) :
    A.leftModuleVectorDualTotalLinearMap M (A.rightModuleTotalAction (A.leftModuleVectorDual M) a φ) =
      (A.leftModuleVectorDualTotalLinearMap M φ).comp (A.leftModuleTotalAction M a) := by
  apply DirectSum.linearMap_ext
  intro t
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  by_cases ht : t = i
  · subst t
    rw [A.leftModuleTotalAction_lof, A.leftModuleVectorDualTotalLinearMap_eval_lof,
      A.leftModuleVectorDualTotalLinearMap_eval_lof]
    change (A.scalarEndEquiv 0).symm
      (((DirectSum.lof k ℤ (fun l => (A.rightModuleEvaluation l).obj (A.leftModuleVectorDual M)) i
        (((A.leftModuleVectorDual M).obj.map (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a).op).hom (φ j))) i).hom x) = _
    rw [DirectSum.lof_apply]
    rfl
  · rw [A.leftModuleTotalAction_lof_off M a t ht, map_zero,
      A.leftModuleVectorDualTotalLinearMap_eval_lof]
    change (A.scalarEndEquiv 0).symm
      (((DFinsupp.single i
        (((A.leftModuleVectorDual M).obj.map (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a).op).hom (φ j)) :
          A.rightModuleTotalSpace (A.leftModuleVectorDual M)) t).hom x) = 0
    rw [DFinsupp.single_eq_of_ne ht]
    simp

theorem rightModuleVectorDualTotalLinearMap_total_action (M : A.RightModule)
    (a : A.totalAlgebra) (φ : A.leftModuleTotalSpace (A.rightModuleVectorDual M))
    (x : A.rightModuleTotalSpace M) :
    A.rightModuleVectorDualTotalLinearMap M (A.leftTotalRepresentation (A.rightModuleVectorDual M) a φ) x =
      A.rightModuleVectorDualTotalLinearMap M φ ((A.rightTotalRepresentation M a).unop x) := by
  obtain ⟨a,rfl⟩ := A.totalAlgebraEquiv.surjective a
  induction a using DFinsupp.induction with
  | h0 => simp
  | ha p b a _ _ ih =>
    rw [(A.totalAlgebraEquiv).map_add,
      (A.leftTotalRepresentation (A.rightModuleVectorDual M)).map_add,
      (A.rightTotalRepresentation M).map_add, MulOpposite.unop_add,
      LinearMap.add_apply, LinearMap.add_apply, map_add, LinearMap.add_apply, map_add, ih]
    congr 1
    rcases p with ⟨i,j⟩
    change A.rightModuleVectorDualTotalLinearMap M
      (A.leftTotalRepresentation (A.rightModuleVectorDual M) (A.totalAlgebraComponent b) φ) x =
        A.rightModuleVectorDualTotalLinearMap M φ ((A.rightTotalRepresentation M (A.totalAlgebraComponent b)).unop x)
    rw [A.leftTotalRepresentation_component, A.rightTotalRepresentation_component]
    exact congrArg (fun f => f x) (A.rightModuleVectorDualTotalLinearMap_component_action M b φ)

theorem leftModuleVectorDualTotalLinearMap_total_action (M : A.LeftModule)
    (a : A.totalAlgebra) (φ : A.rightModuleTotalSpace (A.leftModuleVectorDual M))
    (x : A.leftModuleTotalSpace M) :
    A.leftModuleVectorDualTotalLinearMap M ((A.rightTotalRepresentation (A.leftModuleVectorDual M) a).unop φ) x =
      A.leftModuleVectorDualTotalLinearMap M φ (A.leftTotalRepresentation M a x) := by
  obtain ⟨a,rfl⟩ := A.totalAlgebraEquiv.surjective a
  induction a using DFinsupp.induction with
  | h0 => simp
  | ha p b a _ _ ih =>
    rw [(A.totalAlgebraEquiv).map_add,
      (A.rightTotalRepresentation (A.leftModuleVectorDual M)).map_add,
      (A.leftTotalRepresentation M).map_add, MulOpposite.unop_add,
      LinearMap.add_apply, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, ih]
    congr 1
    rcases p with ⟨i,j⟩
    change A.leftModuleVectorDualTotalLinearMap M
      ((A.rightTotalRepresentation (A.leftModuleVectorDual M) (A.totalAlgebraComponent b)).unop φ) x =
        A.leftModuleVectorDualTotalLinearMap M φ (A.leftTotalRepresentation M (A.totalAlgebraComponent b) x)
    rw [A.rightTotalRepresentation_component, A.leftTotalRepresentation_component]
    exact congrArg (fun f => f x) (A.leftModuleVectorDualTotalLinearMap_component_action M b φ)

end ASGinzburg.ZAlgebra
