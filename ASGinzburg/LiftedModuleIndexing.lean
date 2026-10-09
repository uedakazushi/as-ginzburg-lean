import ASGinzburg.RightModuleAbelian
import ASGinzburg.CutQuiver
import Mathlib.CategoryTheory.Equivalence

/-! Reindexing the existing linear right modules by lifted vertices.
The category uses the actual existing A.Hom spaces and the height bijection;
it is equivalent to the existing indexing category and changes no module
definition or algebra action. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

def liftedModuleIndexEquiv : Q.LiftVertex ≃ A.Objᵒᵖ where
  toFun x := op ⟨Q.height x⟩
  invFun X := Q.heightEquiv.symm X.unop.index
  left_inv x := by
    change Q.heightEquiv.symm (Q.height x)=x
    rw [← Q.heightEquiv_apply]
    exact Q.heightEquiv.symm_apply_apply x
  right_inv X := by
    change op (⟨Q.height (Q.heightEquiv.symm X.unop.index)⟩ : A.Obj)=X
    have hi : Q.height (Q.heightEquiv.symm X.unop.index)=X.unop.index := by
      rw [← Q.heightEquiv_apply]
      exact Q.heightEquiv.apply_symm_apply _
    apply Opposite.unop_injective
    change (⟨Q.height (Q.heightEquiv.symm X.unop.index)⟩ : A.Obj)=X.unop
    rw [hi]

abbrev LiftedModuleIndex := InducedCategory A.Objᵒᵖ (A.liftedModuleIndexEquiv Q)

def liftedModuleIndexFunctor : A.LiftedModuleIndex Q ⥤ A.Objᵒᵖ :=
  inducedFunctor (A.liftedModuleIndexEquiv Q)

noncomputable instance liftedModuleIndexFunctorIsEquivalence :
    (A.liftedModuleIndexFunctor Q).IsEquivalence :=
  Equivalence.inducedFunctorOfEquiv _

noncomputable def liftedModuleIndexWhisker :
    (A.Objᵒᵖ ⥤ ModuleCat.{v} k) ⥤ (A.LiftedModuleIndex Q ⥤ ModuleCat.{v} k) :=
  (Functor.whiskeringLeft _ _ _).obj (A.liftedModuleIndexFunctor Q)

noncomputable instance liftedModuleIndexWhiskerIsEquivalence :
    (A.liftedModuleIndexWhisker Q).IsEquivalence := by
  unfold liftedModuleIndexWhisker
  infer_instance

noncomputable def rightModuleHomOfLiftedComponents {M N : A.RightModule}
    (f : A.liftedModuleIndexFunctor Q ⋙ M.obj ⟶ A.liftedModuleIndexFunctor Q ⋙ N.obj) :
    M ⟶ N := (A.liftedModuleIndexWhisker Q).preimage f

theorem rightModuleHomOfLiftedComponents_whisker {M N : A.RightModule}
    (f : A.liftedModuleIndexFunctor Q ⋙ M.obj ⟶ A.liftedModuleIndexFunctor Q ⋙ N.obj) :
    (A.liftedModuleIndexWhisker Q).map (A.rightModuleHomOfLiftedComponents Q f)=f :=
  Functor.map_preimage _ _

end ASGinzburg.ZAlgebra
