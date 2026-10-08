import ASGinzburg.UnitizationComponentModules

/-! Component recovery on morphisms and finite direct-sum reconstruction.
The bijectivity of the sum map uses the concrete locally unital condition.
Compatibility with the full unitization action is proved separately. -/

namespace ASGinzburg.ZAlgebra
open CategoryTheory Opposite
open scoped ModuleCat.Algebra DirectSum
attribute [local instance 2000] ModuleCat.isModule
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def leftUnitizationComponentHom
    {M N : ModuleCat.{v} A.totalUnitization} (f : M ⟶ N) (i : ℤ) :
    A.leftUnitizationComponentSpace M i →ₗ[k] A.leftUnitizationComponentSpace N i where
  toFun x := ⟨f.hom x, by
    obtain ⟨y,hy⟩ := x.property
    refine ⟨f.hom y,?_⟩
    change (A.totalAlgebraComponent (A.id i) : A.totalUnitization) • f.hom y = f.hom x
    rw [← f.hom.map_smul]
    exact congrArg f.hom hy⟩
  map_add' x y := Subtype.ext (f.hom.map_add x y)
  map_smul' r x := Subtype.ext ((f.hom.restrictScalars k).map_smul r x)

noncomputable def rightUnitizationComponentHom
    {M N : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ} (f : M ⟶ N) (i : ℤ) :
    A.rightUnitizationComponentSpace M i →ₗ[k] A.rightUnitizationComponentSpace N i where
  toFun x := ⟨f.hom x, by
    obtain ⟨y,hy⟩ := x.property
    refine ⟨f.hom y,?_⟩
    change MulOpposite.op (A.totalAlgebraComponent (A.id i) : A.totalUnitization) • f.hom y = f.hom x
    rw [← f.hom.map_smul]
    exact congrArg f.hom hy⟩
  map_add' x y := Subtype.ext (f.hom.map_add x y)
  map_smul' r x := Subtype.ext ((f.hom.restrictScalars k).map_smul r x)

noncomputable def unitizationLeftComponentModuleMap
    {M N : ModuleCat.{v} A.totalUnitization} (f : M ⟶ N) :
    A.unitizationLeftComponentModule M ⟶ A.unitizationLeftComponentModule N where
  app X := ModuleCat.ofHom (A.leftUnitizationComponentHom f X.index)
  naturality := by
    intro X Y a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change A.leftUnitizationComponentSpace M X.index at x
    exact f.hom.map_smul (A.totalAlgebraComponent a : A.totalUnitization) x.val

noncomputable def unitizationRightComponentModuleMap
    {M N : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ} (f : M ⟶ N) :
    A.unitizationRightComponentModule M ⟶ A.unitizationRightComponentModule N where
  app X := ModuleCat.ofHom (A.rightUnitizationComponentHom f X.unop.index)
  naturality := by
    intro X Y a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change A.rightUnitizationComponentSpace M X.unop.index at x
    exact f.hom.map_smul (MulOpposite.op (A.totalAlgebraComponent a.unop : A.totalUnitization)) x.val

noncomputable def unitizationLeftComponentModuleFunctor :
    ModuleCat.{v} A.totalUnitization ⥤ A.LeftModule where
  obj := A.unitizationLeftComponentModule
  map := A.unitizationLeftComponentModuleMap
  map_id M := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl

noncomputable def unitizationRightComponentModuleFunctor :
    ModuleCat.{v} A.totalUnitizationᵐᵒᵖ ⥤ A.RightModule where
  obj := A.unitizationRightComponentModule
  map := A.unitizationRightComponentModuleMap
  map_id M := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl

noncomputable def leftLocallyUnitalComponentFunctor : A.LeftLocallyUnitalModule ⥤ A.LeftModule where
  obj M := A.unitizationLeftComponentModule M.obj
  map f := A.unitizationLeftComponentModuleMap f
  map_id M := (A.unitizationLeftComponentModuleFunctor).map_id M.obj
  map_comp f g := (A.unitizationLeftComponentModuleFunctor).map_comp f g

noncomputable def rightLocallyUnitalComponentFunctor : A.RightLocallyUnitalModule ⥤ A.RightModule where
  obj M := A.unitizationRightComponentModule M.obj
  map f := A.unitizationRightComponentModuleMap f
  map_id M := (A.unitizationRightComponentModuleFunctor).map_id M.obj
  map_comp f g := (A.unitizationRightComponentModuleFunctor).map_comp f g

end ASGinzburg.ZAlgebra
