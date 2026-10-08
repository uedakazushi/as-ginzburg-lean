import ASGinzburg.FiniteDiagramClosureMaps
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-! The actual finite-dimensional full subcategories inherit kernels, cokernels and Abelian structure.
The scoped instance erasure avoids an unresolved max-universe inference in the pinned mathlib;
its scope is a single declaration and it does not change any exported instance. -/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v w'
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)
@[local instance] def smallModuleCatLimits : HasLimitsOfSize.{0,0} (ModuleCat.{v} k) :=
  ModuleCat.hasLimitsOfSize.{0,0,v,u}
@[local instance] def smallRightModuleLimits : HasLimitsOfSize.{0,0} A.RightModule where
  has_limits_of_shape J := A.rightModuleHasLimitsOfShape J

attribute [-instance] ModuleCat.instHasLimitsOfSize in
theorem rightFiniteDimensional_product {I : Type} [Finite I] (M : I → A.RightModule)
    (hM : ∀ i, A.rightFiniteDimensionalProperty (M i)) :
    A.rightFiniteDimensionalProperty (∏ᶜ M) := by
  letI : ∀ i, Module.Finite k (A.rightModuleTotalFunctor.obj (M i)) := fun i => by
    letI : Module.Finite k (A.rightModuleTotalSpace (M i)) := hM i
    exact Module.Finite.equiv (A.rightModuleTotalFunctorObjIso (M i)).symm.toLinearEquiv
  let e₀ : A.rightModuleTotalFunctor.obj (∏ᶜ M) ≅
      ∏ᶜ (fun i => A.rightModuleTotalFunctor.obj (M i)) :=
    PreservesProduct.iso A.rightModuleTotalFunctor M
  let e₁ : (∏ᶜ (fun i => A.rightModuleTotalFunctor.obj (M i))) ≅
      ModuleCat.of k (∀ i, A.rightModuleTotalFunctor.obj (M i)) :=
    ModuleCat.piIsoPi.{u,0,v} (fun i => A.rightModuleTotalFunctor.obj (M i))
  let e := e₀ ≪≫ e₁
  letI : Module.Finite k (A.rightModuleTotalFunctor.obj (∏ᶜ M)) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  exact Module.Finite.equiv (A.rightModuleTotalFunctorObjIso (∏ᶜ M)).toLinearEquiv

attribute [-instance] ModuleCat.instHasLimitsOfSize in
theorem rightFiniteDimensional_coproduct {I : Type} [Finite I] (M : I → A.RightModule)
    (hM : ∀ i, A.rightFiniteDimensionalProperty (M i)) :
    A.rightFiniteDimensionalProperty (∐ M) := by
  letI : HasFiniteBiproducts A.RightModule := Abelian.hasFiniteBiproducts
  let e := (biproduct.isoCoproduct M).symm ≪≫ biproduct.isoProduct M
  exact A.rightFiniteDimensional_of_mono e.hom (A.rightFiniteDimensional_product M hM)

attribute [-instance] ModuleCat.instHasLimitsOfSize in
theorem rightFiniteDimensionalProperty_closedUnderFiniteLimits
    (J : Type) [SmallCategory J] [Finite J] :
    ClosedUnderLimitsOfShape J A.rightFiniteDimensionalProperty := by
  intro F c hc hF
  letI := ASGinzburg.limitConeProductMono c hc
  exact A.rightFiniteDimensional_of_mono (Pi.lift (fun j => c.π.app j))
    (A.rightFiniteDimensional_product (fun j => F.obj j) hF)

attribute [-instance] ModuleCat.instHasLimitsOfSize in
theorem rightFiniteDimensionalProperty_closedUnderFiniteColimits
    (J : Type) [SmallCategory J] [Finite J] :
    ClosedUnderColimitsOfShape J A.rightFiniteDimensionalProperty := by
  intro F c hc hF
  letI := ASGinzburg.colimitCoconeCoproductEpi c hc
  exact A.rightFiniteDimensional_of_epi (Sigma.desc (fun j => c.ι.app j))
    (A.rightFiniteDimensional_coproduct (fun j => F.obj j) hF)

attribute [-instance] ModuleCat.instHasLimitsOfSize in
noncomputable instance rightFiniteDimensionalHasLimitsOfShape
    (J : Type) [SmallCategory J] [Finite J] : HasLimitsOfShape J A.RightFiniteDimensional :=
  hasLimitsOfShape_of_closedUnderLimits (A.rightFiniteDimensionalProperty_closedUnderFiniteLimits J)

attribute [-instance] ModuleCat.instHasLimitsOfSize in
noncomputable instance rightFiniteDimensionalHasColimitsOfShape
    (J : Type) [SmallCategory J] [Finite J] : HasColimitsOfShape J A.RightFiniteDimensional :=
  hasColimitsOfShape_of_closedUnderColimits (A.rightFiniteDimensionalProperty_closedUnderFiniteColimits J)

attribute [-instance] ModuleCat.instHasLimitsOfSize in
noncomputable instance rightFiniteDimensionalInclusionCreatesLimitsOfShape
    (J : Type) [SmallCategory J] [Finite J] :
    CreatesLimitsOfShape J A.rightFiniteDimensionalProperty.ι :=
  createsLimitsOfShapeFullSubcategoryInclusion (A.rightFiniteDimensionalProperty_closedUnderFiniteLimits J)

attribute [-instance] ModuleCat.instHasLimitsOfSize in
noncomputable instance rightFiniteDimensionalInclusionCreatesColimitsOfShape
    (J : Type) [SmallCategory J] [Finite J] :
    CreatesColimitsOfShape J A.rightFiniteDimensionalProperty.ι :=
  createsColimitsOfShapeFullSubcategoryInclusion (A.rightFiniteDimensionalProperty_closedUnderFiniteColimits J)

attribute [-instance] ModuleCat.instHasLimitsOfSize in
noncomputable instance rightFiniteDimensionalHasFiniteProducts : HasFiniteProducts A.RightFiniteDimensional where
  out _ := inferInstance

attribute [-instance] ModuleCat.instHasLimitsOfSize in
set_option maxHeartbeats 800000 in
noncomputable instance rightFiniteDimensionalCoimageImageComparisonIsIso
    {M N : A.RightFiniteDimensional} (f : M ⟶ N) : IsIso (Abelian.coimageImageComparison f) := by
  haveI : IsIso (A.rightFiniteDimensionalProperty.ι.map (Abelian.coimageImageComparison f)) := by
    rw [Arrow.isIso_iff_isIso_of_isIso
      (Abelian.PreservesCoimageImageComparison.iso A.rightFiniteDimensionalProperty.ι f).hom]
    infer_instance
  exact isIso_of_reflects_iso _ A.rightFiniteDimensionalProperty.ι

attribute [-instance] ModuleCat.instHasLimitsOfSize in
noncomputable instance rightFiniteDimensionalAbelian : Abelian A.RightFiniteDimensional :=
  Abelian.ofCoimageImageComparisonIsIso

attribute [-instance] ModuleCat.instHasLimitsOfSize in
noncomputable instance rightFiniteDimensionalInclusionPreservesFiniteLimits :
    PreservesFiniteLimits A.rightFiniteDimensionalProperty.ι where
  preservesFiniteLimits _ := inferInstance

attribute [-instance] ModuleCat.instHasLimitsOfSize in
noncomputable instance rightFiniteDimensionalInclusionPreservesFiniteColimits :
    PreservesFiniteColimits A.rightFiniteDimensionalProperty.ι where
  preservesFiniteColimits _ := inferInstance
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v w'
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)
@[local instance] def smallLeftModuleLimits : HasLimitsOfSize.{0,0} A.LeftModule where
  has_limits_of_shape J := A.leftModuleHasLimitsOfShape J

attribute [-instance] ModuleCat.instHasLimitsOfSize in
theorem leftFiniteDimensional_product {I : Type} [Finite I] (M : I → A.LeftModule)
    (hM : ∀ i, A.leftFiniteDimensionalProperty (M i)) :
    A.leftFiniteDimensionalProperty (∏ᶜ M) := by
  letI : ∀ i, Module.Finite k (A.leftModuleTotalFunctor.obj (M i)) := fun i => by
    letI : Module.Finite k (A.leftModuleTotalSpace (M i)) := hM i
    exact Module.Finite.equiv (A.leftModuleTotalFunctorObjIso (M i)).symm.toLinearEquiv
  let e₀ : A.leftModuleTotalFunctor.obj (∏ᶜ M) ≅
      ∏ᶜ (fun i => A.leftModuleTotalFunctor.obj (M i)) :=
    PreservesProduct.iso A.leftModuleTotalFunctor M
  let e₁ : (∏ᶜ (fun i => A.leftModuleTotalFunctor.obj (M i))) ≅
      ModuleCat.of k (∀ i, A.leftModuleTotalFunctor.obj (M i)) :=
    ModuleCat.piIsoPi.{u,0,v} (fun i => A.leftModuleTotalFunctor.obj (M i))
  let e := e₀ ≪≫ e₁
  letI : Module.Finite k (A.leftModuleTotalFunctor.obj (∏ᶜ M)) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  exact Module.Finite.equiv (A.leftModuleTotalFunctorObjIso (∏ᶜ M)).toLinearEquiv

attribute [-instance] ModuleCat.instHasLimitsOfSize in
theorem leftFiniteDimensional_coproduct {I : Type} [Finite I] (M : I → A.LeftModule)
    (hM : ∀ i, A.leftFiniteDimensionalProperty (M i)) :
    A.leftFiniteDimensionalProperty (∐ M) := by
  letI : HasFiniteBiproducts A.LeftModule := Abelian.hasFiniteBiproducts
  let e := (biproduct.isoCoproduct M).symm ≪≫ biproduct.isoProduct M
  exact A.leftFiniteDimensional_of_mono e.hom (A.leftFiniteDimensional_product M hM)

attribute [-instance] ModuleCat.instHasLimitsOfSize in
theorem leftFiniteDimensionalProperty_closedUnderFiniteLimits
    (J : Type) [SmallCategory J] [Finite J] :
    ClosedUnderLimitsOfShape J A.leftFiniteDimensionalProperty := by
  intro F c hc hF
  letI := ASGinzburg.limitConeProductMono c hc
  exact A.leftFiniteDimensional_of_mono (Pi.lift (fun j => c.π.app j))
    (A.leftFiniteDimensional_product (fun j => F.obj j) hF)

attribute [-instance] ModuleCat.instHasLimitsOfSize in
theorem leftFiniteDimensionalProperty_closedUnderFiniteColimits
    (J : Type) [SmallCategory J] [Finite J] :
    ClosedUnderColimitsOfShape J A.leftFiniteDimensionalProperty := by
  intro F c hc hF
  letI := ASGinzburg.colimitCoconeCoproductEpi c hc
  exact A.leftFiniteDimensional_of_epi (Sigma.desc (fun j => c.ι.app j))
    (A.leftFiniteDimensional_coproduct (fun j => F.obj j) hF)

attribute [-instance] ModuleCat.instHasLimitsOfSize in
noncomputable instance leftFiniteDimensionalHasLimitsOfShape
    (J : Type) [SmallCategory J] [Finite J] : HasLimitsOfShape J A.LeftFiniteDimensional :=
  hasLimitsOfShape_of_closedUnderLimits (A.leftFiniteDimensionalProperty_closedUnderFiniteLimits J)

attribute [-instance] ModuleCat.instHasLimitsOfSize in
noncomputable instance leftFiniteDimensionalHasColimitsOfShape
    (J : Type) [SmallCategory J] [Finite J] : HasColimitsOfShape J A.LeftFiniteDimensional :=
  hasColimitsOfShape_of_closedUnderColimits (A.leftFiniteDimensionalProperty_closedUnderFiniteColimits J)

attribute [-instance] ModuleCat.instHasLimitsOfSize in
noncomputable instance leftFiniteDimensionalInclusionCreatesLimitsOfShape
    (J : Type) [SmallCategory J] [Finite J] :
    CreatesLimitsOfShape J A.leftFiniteDimensionalProperty.ι :=
  createsLimitsOfShapeFullSubcategoryInclusion (A.leftFiniteDimensionalProperty_closedUnderFiniteLimits J)

attribute [-instance] ModuleCat.instHasLimitsOfSize in
noncomputable instance leftFiniteDimensionalInclusionCreatesColimitsOfShape
    (J : Type) [SmallCategory J] [Finite J] :
    CreatesColimitsOfShape J A.leftFiniteDimensionalProperty.ι :=
  createsColimitsOfShapeFullSubcategoryInclusion (A.leftFiniteDimensionalProperty_closedUnderFiniteColimits J)

attribute [-instance] ModuleCat.instHasLimitsOfSize in
noncomputable instance leftFiniteDimensionalHasFiniteProducts : HasFiniteProducts A.LeftFiniteDimensional where
  out _ := inferInstance

attribute [-instance] ModuleCat.instHasLimitsOfSize in
set_option maxHeartbeats 800000 in
noncomputable instance leftFiniteDimensionalCoimageImageComparisonIsIso
    {M N : A.LeftFiniteDimensional} (f : M ⟶ N) : IsIso (Abelian.coimageImageComparison f) := by
  haveI : IsIso (A.leftFiniteDimensionalProperty.ι.map (Abelian.coimageImageComparison f)) := by
    rw [Arrow.isIso_iff_isIso_of_isIso
      (Abelian.PreservesCoimageImageComparison.iso A.leftFiniteDimensionalProperty.ι f).hom]
    infer_instance
  exact isIso_of_reflects_iso _ A.leftFiniteDimensionalProperty.ι

attribute [-instance] ModuleCat.instHasLimitsOfSize in
noncomputable instance leftFiniteDimensionalAbelian : Abelian A.LeftFiniteDimensional :=
  Abelian.ofCoimageImageComparisonIsIso

attribute [-instance] ModuleCat.instHasLimitsOfSize in
noncomputable instance leftFiniteDimensionalInclusionPreservesFiniteLimits :
    PreservesFiniteLimits A.leftFiniteDimensionalProperty.ι where
  preservesFiniteLimits _ := inferInstance

attribute [-instance] ModuleCat.instHasLimitsOfSize in
noncomputable instance leftFiniteDimensionalInclusionPreservesFiniteColimits :
    PreservesFiniteColimits A.leftFiniteDimensionalProperty.ι where
  preservesFiniteColimits _ := inferInstance
end ASGinzburg.ZAlgebra
