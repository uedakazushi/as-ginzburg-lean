import ASGinzburg.FoundationRingComponentActions

/-! Actual images of the component projectors recover the original
component vector spaces and contravariant A.Hom actions. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
attribute [local instance 2000] ModuleCat.isModule
universe u
variable {k : Type u} [Field k] (A : ZAlgebra.{u,u} k) (Q : CutQuiver)

noncomputable abbrev foundationRingRightComponentSpace
    (M : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) (i : Q.Vertex) :=
  LinearMap.range (A.foundationRingRightProjection Q M i)

theorem foundationRingRightProjection_range_fixed
    (M : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) (i : Q.Vertex)
    (x : A.foundationRingRightComponentSpace Q M i) :
    A.foundationRingRightProjection Q M i x=x.val := by
  obtain ⟨y,hy⟩ := x.property
  rw [←hy]
  exact LinearMap.congr_fun (A.foundationRingRightProjection_idempotent Q M i) y

noncomputable def foundationRingRightComponentMap
    (M : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) {i j : Q.Vertex}
    (a : A.Hom (i.val : ℤ) (j.val : ℤ)) :
    A.foundationRingRightComponentSpace Q M j →ₗ[k]
      A.foundationRingRightComponentSpace Q M i where
  toFun x := ⟨A.foundationRingRightComponentAction Q M a x,by
    refine ⟨A.foundationRingRightComponentAction Q M a x,?_⟩
    have h := A.foundationRingRightComponentAction_comp Q M (A.id (i.val : ℤ)) a
    rw [A.id_comp] at h
    exact LinearMap.congr_fun h x⟩
  map_add' x y := Subtype.ext ((A.foundationRingRightComponentAction Q M a).map_add x y)
  map_smul' c x := Subtype.ext ((A.foundationRingRightComponentAction Q M a).map_smul c x)

theorem foundationRingRightComponentMap_id
    (M : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) (i : Q.Vertex) :
    A.foundationRingRightComponentMap Q M (A.id (i.val : ℤ))=LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact Subtype.ext (A.foundationRingRightProjection_range_fixed Q M i x)

theorem foundationRingRightComponentMap_comp
    (M : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) {i j l : Q.Vertex}
    (a : A.Hom (i.val : ℤ) (j.val : ℤ)) (b : A.Hom (j.val : ℤ) (l.val : ℤ)) :
    (A.foundationRingRightComponentMap Q M a).comp (A.foundationRingRightComponentMap Q M b)=
      A.foundationRingRightComponentMap Q M (A.comp b a) := by
  apply LinearMap.ext
  intro x
  exact Subtype.ext (LinearMap.congr_fun (A.foundationRingRightComponentAction_comp Q M a b) x)

noncomputable def foundationRingRightActionLinear
    (M : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) (i j : Q.Vertex) :
    A.Hom (i.val : ℤ) (j.val : ℤ) →ₗ[k] Module.End k M where
  toFun := A.foundationRingRightComponentAction Q M
  map_add' a b := by
    apply LinearMap.ext
    intro x
    change MulOpposite.op (A.foundationAlgebraComponentLinear Q i j (a+b)) • x=_
    rw [map_add,MulOpposite.op_add,add_smul]
    rfl
  map_smul' c a := by
    apply LinearMap.ext
    intro x
    change MulOpposite.op (A.foundationAlgebraComponentLinear Q i j (c • a)) • x=_
    rw [map_smul,MulOpposite.op_smul]
    exact smul_assoc c _ x

noncomputable def foundationRingRightRangeActionLinear
    (M : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) (i j : Q.Vertex) :
    A.Hom (i.val : ℤ) (j.val : ℤ) →ₗ[k]
      (A.foundationRingRightComponentSpace Q M j →ₗ[k] A.foundationRingRightComponentSpace Q M i) where
  toFun := A.foundationRingRightComponentMap Q M
  map_add' a b := by
    apply LinearMap.ext
    intro x
    exact Subtype.ext (LinearMap.congr_fun ((A.foundationRingRightActionLinear Q M i j).map_add a b) x)
  map_smul' c a := by
    apply LinearMap.ext
    intro x
    exact Subtype.ext (LinearMap.congr_fun ((A.foundationRingRightActionLinear Q M i j).map_smul c a) x)

end ASGinzburg.ZAlgebra
