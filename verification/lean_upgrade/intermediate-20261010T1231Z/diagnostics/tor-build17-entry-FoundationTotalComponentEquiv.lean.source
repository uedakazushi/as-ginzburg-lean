import ASGinzburg.FoundationTotalComponentActions
import ASGinzburg.FoundationTotalScalarComparison
import ASGinzburg.FoundationRingComponentSpaces

/-! The image of each genuine total-module idempotent is linearly
isomorphic to the original component, by coordinate extraction. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
attribute [local instance 2000] ModuleCat.isModule
universe u
variable {k : Type u} [Field k] (A : ZAlgebra.{u,u} k) (Q : CutQuiver)

noncomputable def foundationRightTotalComponentEquiv
    (M : A.FoundationRightModule Q) (i : Q.Vertex) :
    A.foundationRingRightComponentSpace Q (A.foundationRightTotalModule Q M) i ≃ₗ[k]
      (A.foundationRightEvaluation Q i).obj M := by
  classical
  exact
    { toFun := fun x => x.val i
      invFun := fun x => ⟨Pi.single i x,⟨Pi.single i x,by
        rw [A.foundationRingRightProjection_totalModule_apply Q M i]
        simp⟩⟩
      left_inv := fun x => Subtype.ext (by
        have h := A.foundationRingRightProjection_range_fixed Q
          (A.foundationRightTotalModule Q M) i x
        rw [A.foundationRingRightProjection_totalModule_apply Q M i] at h
        exact h)
      right_inv := fun x => by simp
      map_add' := fun x y => rfl
      map_smul' := fun c x => by
        change (c • x.val) i=c • x.val i
        exact congrFun (A.foundationRightTotalModule_scalar_smul Q M c x.val) i }

theorem foundationRightTotalComponentEquiv_apply
    (M : A.FoundationRightModule Q) (i : Q.Vertex)
    (x : A.foundationRingRightComponentSpace Q (A.foundationRightTotalModule Q M) i) :
    A.foundationRightTotalComponentEquiv Q M i x=x.val i := rfl

theorem foundationRightTotalComponentEquiv_symm_apply
    (M : A.FoundationRightModule Q) (i : Q.Vertex)
    (x : (A.foundationRightEvaluation Q i).obj M) :
    ((A.foundationRightTotalComponentEquiv Q M i).symm x).val=Pi.single i x := rfl

end ASGinzburg.ZAlgebra
