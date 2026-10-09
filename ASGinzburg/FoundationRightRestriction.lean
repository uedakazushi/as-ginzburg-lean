import ASGinzburg.LinearPresheafAbelian
import ASGinzburg.RightModuleHomology
import ASGinzburg.CutQuiver
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! Actual sheet-zero right representations and restriction of the
existing linear right modules, with their original component action. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

abbrev FoundationRightObj :=
  InducedCategory A.Objᵒᵖ (fun i : Q.Vertex => op (⟨(i.val : ℤ)⟩ : A.Obj))

def foundationRightInclusion : A.FoundationRightObj Q ⥤ A.Objᵒᵖ :=
  inducedFunctor (fun i : Q.Vertex => op (⟨(i.val : ℤ)⟩ : A.Obj))

instance foundationRightInclusionAdditive : (A.foundationRightInclusion Q).Additive := by
  dsimp [foundationRightInclusion]
  infer_instance

instance foundationRightInclusionLinear : (A.foundationRightInclusion Q).Linear k := by
  dsimp [foundationRightInclusion]
  infer_instance

abbrev FoundationRightModule := LinearPresheaf k (A.FoundationRightObj Q)

def foundationRestriction : A.RightModule ⥤ A.FoundationRightModule Q where
  obj M := ⟨A.foundationRightInclusion Q ⋙ M.obj,by
    letI := M.property.1
    letI := M.property.2
    constructor <;> infer_instance⟩
  map f := whiskerLeft (A.foundationRightInclusion Q) f

instance foundationRestrictionAdditive : (A.foundationRestriction Q).Additive where
  map_add := by intro M N f g; rfl

instance foundationRestrictionLinear : (A.foundationRestriction Q).Linear k where
  map_smul := by intro M N f r; rfl

def foundationRightEvaluation (i : Q.Vertex) :
    A.FoundationRightModule Q ⥤ ModuleCat.{v} k :=
  (linearPresheafProperty k (A.FoundationRightObj Q)).ι ⋙
    (evaluation (A.FoundationRightObj Q) (ModuleCat.{v} k)).obj i

theorem foundationRestriction_evaluation (i : Q.Vertex) :
    A.foundationRestriction Q ⋙ A.foundationRightEvaluation Q i=
      A.rightModuleEvaluation (i.val : ℤ) := rfl

end ASGinzburg.ZAlgebra
