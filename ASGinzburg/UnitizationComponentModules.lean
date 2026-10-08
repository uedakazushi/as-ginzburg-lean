import ASGinzburg.UnitizationComponentActions

/-! The images of the component idempotents of any module over the unitization
recover additive k-linear left or right presheaves. Recovering the entire
module by their direct sum additionally requires the locally unital condition. -/

namespace ASGinzburg.ZAlgebra
open CategoryTheory Opposite
open scoped ModuleCat.Algebra DirectSum
attribute [local instance 2000] ModuleCat.isModule
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable abbrev leftUnitizationComponentSpace (M : ModuleCat.{v} A.totalUnitization) (i : ℤ) :=
  LinearMap.range (A.leftUnitizationProjection M i)

noncomputable abbrev rightUnitizationComponentSpace (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ)
    (i : ℤ) := LinearMap.range (A.rightUnitizationProjection M i)

theorem leftUnitizationProjection_range_fixed (M : ModuleCat.{v} A.totalUnitization) (i : ℤ)
    (x : A.leftUnitizationComponentSpace M i) : A.leftUnitizationProjection M i x = x.val := by
  obtain ⟨y,hy⟩ := x.property
  rw [← hy]
  exact LinearMap.congr_fun (A.leftUnitizationProjection_idempotent M i) y

theorem rightUnitizationProjection_range_fixed (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ) (i : ℤ)
    (x : A.rightUnitizationComponentSpace M i) : A.rightUnitizationProjection M i x = x.val := by
  obtain ⟨y,hy⟩ := x.property
  rw [← hy]
  exact LinearMap.congr_fun (A.rightUnitizationProjection_idempotent M i) y

noncomputable def leftUnitizationComponentMap (M : ModuleCat.{v} A.totalUnitization)
    {i j : ℤ} (a : A.Hom i j) :
    A.leftUnitizationComponentSpace M i →ₗ[k] A.leftUnitizationComponentSpace M j where
  toFun x := ⟨A.leftUnitizationComponentAction M a x, by
    refine ⟨A.leftUnitizationComponentAction M a x, ?_⟩
    have h := A.leftUnitizationComponentAction_comp M a (A.id j)
    rw [A.comp_id] at h
    exact LinearMap.congr_fun h x⟩
  map_add' x y := Subtype.ext ((A.leftUnitizationComponentAction M a).map_add x y)
  map_smul' r x := Subtype.ext ((A.leftUnitizationComponentAction M a).map_smul r x)

noncomputable def rightUnitizationComponentMap (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ)
    {i j : ℤ} (a : A.Hom i j) :
    A.rightUnitizationComponentSpace M j →ₗ[k] A.rightUnitizationComponentSpace M i where
  toFun x := ⟨A.rightUnitizationComponentAction M a x, by
    refine ⟨A.rightUnitizationComponentAction M a x, ?_⟩
    have h := A.rightUnitizationComponentAction_comp M (A.id i) a
    rw [A.id_comp] at h
    exact LinearMap.congr_fun h x⟩
  map_add' x y := Subtype.ext ((A.rightUnitizationComponentAction M a).map_add x y)
  map_smul' r x := Subtype.ext ((A.rightUnitizationComponentAction M a).map_smul r x)

theorem leftUnitizationComponentMap_id (M : ModuleCat.{v} A.totalUnitization) (i : ℤ) :
    A.leftUnitizationComponentMap M (A.id i) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact A.leftUnitizationProjection_range_fixed M i x

theorem rightUnitizationComponentMap_id (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ) (i : ℤ) :
    A.rightUnitizationComponentMap M (A.id i) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact A.rightUnitizationProjection_range_fixed M i x

theorem leftUnitizationComponentMap_comp (M : ModuleCat.{v} A.totalUnitization)
    {i j l : ℤ} (a : A.Hom i j) (b : A.Hom j l) :
    (A.leftUnitizationComponentMap M b).comp (A.leftUnitizationComponentMap M a) =
      A.leftUnitizationComponentMap M (A.comp b a) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (A.leftUnitizationComponentAction_comp M a b) x

theorem rightUnitizationComponentMap_comp (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ)
    {i j l : ℤ} (a : A.Hom i j) (b : A.Hom j l) :
    (A.rightUnitizationComponentMap M a).comp (A.rightUnitizationComponentMap M b) =
      A.rightUnitizationComponentMap M (A.comp b a) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (A.rightUnitizationComponentAction_comp M a b) x


noncomputable def leftUnitizationActionLinear (M : ModuleCat.{v} A.totalUnitization) (i j : ℤ) :
    A.Hom i j →ₗ[k] Module.End k M where
  toFun := A.leftUnitizationComponentAction M
  map_add' a b := by
    apply LinearMap.ext
    intro x
    change A.totalUnitizationComponentLinear i j (a + b) • x =
      A.totalUnitizationComponentLinear i j a • x + A.totalUnitizationComponentLinear i j b • x
    rw [map_add, add_smul]
  map_smul' r a := by
    apply LinearMap.ext
    intro x
    change A.totalUnitizationComponentLinear i j (r • a) • x =
      r • (A.totalUnitizationComponentLinear i j a • x)
    rw [map_smul]
    exact smul_assoc r _ x

noncomputable def rightUnitizationActionLinear (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ) (i j : ℤ) :
    A.Hom i j →ₗ[k] Module.End k M where
  toFun := A.rightUnitizationComponentAction M
  map_add' a b := by
    apply LinearMap.ext
    intro x
    change MulOpposite.op (A.totalUnitizationComponentLinear i j (a + b)) • x =
      MulOpposite.op (A.totalUnitizationComponentLinear i j a) • x +
        MulOpposite.op (A.totalUnitizationComponentLinear i j b) • x
    rw [map_add, MulOpposite.op_add, add_smul]
  map_smul' r a := by
    apply LinearMap.ext
    intro x
    change MulOpposite.op (A.totalUnitizationComponentLinear i j (r • a)) • x =
      r • (MulOpposite.op (A.totalUnitizationComponentLinear i j a) • x)
    rw [map_smul, MulOpposite.op_smul]
    exact smul_assoc r _ x

noncomputable def leftUnitizationRangeActionLinear (M : ModuleCat.{v} A.totalUnitization) (i j : ℤ) :
    A.Hom i j →ₗ[k] (A.leftUnitizationComponentSpace M i →ₗ[k] A.leftUnitizationComponentSpace M j) where
  toFun := A.leftUnitizationComponentMap M
  map_add' a b := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun ((A.leftUnitizationActionLinear M i j).map_add a b) x
  map_smul' r a := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun ((A.leftUnitizationActionLinear M i j).map_smul r a) x

noncomputable def rightUnitizationRangeActionLinear (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ) (i j : ℤ) :
    A.Hom i j →ₗ[k] (A.rightUnitizationComponentSpace M j →ₗ[k] A.rightUnitizationComponentSpace M i) where
  toFun := A.rightUnitizationComponentMap M
  map_add' a b := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun ((A.rightUnitizationActionLinear M i j).map_add a b) x
  map_smul' r a := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun ((A.rightUnitizationActionLinear M i j).map_smul r a) x

noncomputable def unitizationLeftComponentFunctor (M : ModuleCat.{v} A.totalUnitization) :
    A.Obj ⥤ ModuleCat.{v} k where
  obj X := ModuleCat.of k (A.leftUnitizationComponentSpace M X.index)
  map a := ModuleCat.ofHom (A.leftUnitizationComponentMap M a)
  map_id X := by
    apply ModuleCat.hom_ext
    exact A.leftUnitizationComponentMap_id M X.index
  map_comp a b := by
    apply ModuleCat.hom_ext
    exact (A.leftUnitizationComponentMap_comp M a b).symm

noncomputable def unitizationRightComponentFunctor (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ) :
    A.Objᵒᵖ ⥤ ModuleCat.{v} k where
  obj X := ModuleCat.of k (A.rightUnitizationComponentSpace M X.unop.index)
  map a := ModuleCat.ofHom (A.rightUnitizationComponentMap M a.unop)
  map_id X := by
    apply ModuleCat.hom_ext
    exact A.rightUnitizationComponentMap_id M X.unop.index
  map_comp a b := by
    apply ModuleCat.hom_ext
    exact (A.rightUnitizationComponentMap_comp M b.unop a.unop).symm

instance unitizationLeftComponentFunctorAdditive (M : ModuleCat.{v} A.totalUnitization) :
    (A.unitizationLeftComponentFunctor M).Additive where
  map_add := by
    intro X Y a b
    apply ModuleCat.hom_ext
    exact (A.leftUnitizationRangeActionLinear M X.index Y.index).map_add a b

instance unitizationRightComponentFunctorAdditive (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ) :
    (A.unitizationRightComponentFunctor M).Additive where
  map_add := by
    intro X Y a b
    apply ModuleCat.hom_ext
    exact (A.rightUnitizationRangeActionLinear M Y.unop.index X.unop.index).map_add a.unop b.unop

instance unitizationLeftComponentFunctorLinear (M : ModuleCat.{v} A.totalUnitization) :
    (A.unitizationLeftComponentFunctor M).Linear k where
  map_smul := by
    intro X Y a r
    apply ModuleCat.hom_ext
    exact (A.leftUnitizationRangeActionLinear M X.index Y.index).map_smul r a

instance unitizationRightComponentFunctorLinear (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ) :
    (A.unitizationRightComponentFunctor M).Linear k where
  map_smul := by
    intro X Y a r
    apply ModuleCat.hom_ext
    exact (A.rightUnitizationRangeActionLinear M Y.unop.index X.unop.index).map_smul r a.unop

noncomputable def unitizationLeftComponentModule (M : ModuleCat.{v} A.totalUnitization) : A.LeftModule :=
  ⟨A.unitizationLeftComponentFunctor M, ⟨inferInstance,inferInstance⟩⟩

noncomputable def unitizationRightComponentModule (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ) : A.RightModule :=
  ⟨A.unitizationRightComponentFunctor M, ⟨inferInstance,inferInstance⟩⟩

end ASGinzburg.ZAlgebra
