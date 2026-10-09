import ASGinzburg.FoundationRingComponentMaps
import ASGinzburg.FoundationTotalScalarComparison

/-! Orthogonal idempotents with sum one give a genuine finite
component decomposition of every foundation-ring module. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
attribute [local instance 2000] ModuleCat.isModule
universe u
variable {k : Type u} [Field k] (A : ZAlgebra.{u,u} k) (Q : CutQuiver)

noncomputable def foundationRingRightComponentSum
    (M : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) :
    A.foundationRightTotalSpace Q (A.foundationRingRightComponentModule Q M) →ₗ[k] M where
  toFun x := ∑ i : Q.Vertex, (x i).val
  map_add' x y := by
    change (∑ i : Q.Vertex,((x i).val+(y i).val))=_
    exact Finset.sum_add_distrib
  map_smul' c x := by
    change (∑ i : Q.Vertex,c • (x i).val)=_
    rw [Finset.smul_sum]
    rfl

theorem foundationRingRightProjection_componentSum
    (M : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) (i : Q.Vertex)
    (x : A.foundationRightTotalSpace Q (A.foundationRingRightComponentModule Q M)) :
    A.foundationRingRightProjection Q M i (A.foundationRingRightComponentSum Q M x)=(x i).val := by
  classical
  change A.foundationRingRightProjection Q M i (∑ j : Q.Vertex,(x j).val)=_
  rw [map_sum,Finset.sum_eq_single i]
  · exact A.foundationRingRightProjection_range_fixed Q M i (x i)
  · intro j _ hji
    have h := LinearMap.congr_fun (A.foundationRingRightProjection_orthogonal Q M i j (Ne.symm hji)) (x j).val
    change A.foundationRingRightProjection Q M i (A.foundationRingRightProjection Q M j (x j).val)=0 at h
    rw [A.foundationRingRightProjection_range_fixed Q M j (x j)] at h
    exact h
  · simp

theorem foundationRingRightProjection_sum
    (M : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) (x : M) :
    (∑ i : Q.Vertex,A.foundationRingRightProjection Q M i x)=x := by
  classical
  change (∑ i : Q.Vertex,MulOpposite.op ((A.foundationComponents Q).totalIdempotent i) • x)=x
  rw [←Finset.sum_smul]
  change (∑ i : Q.Vertex,MulOpposite.opAddEquiv ((A.foundationComponents Q).totalIdempotent i)) • x=x
  rw [←map_sum,(A.foundationComponents Q).sum_totalIdempotent]
  exact one_smul _ x

noncomputable def foundationRingRightComponentSumEquiv
    (M : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) :
    A.foundationRightTotalSpace Q (A.foundationRingRightComponentModule Q M) ≃ₗ[k] M where
  toLinearMap := A.foundationRingRightComponentSum Q M
  invFun x i := ⟨A.foundationRingRightProjection Q M i x,⟨x,rfl⟩⟩
  left_inv x := by
    funext i
    exact Subtype.ext (A.foundationRingRightProjection_componentSum Q M i x)
  right_inv x := A.foundationRingRightProjection_sum Q M x

end ASGinzburg.ZAlgebra
