import ASGinzburg.Representables
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-!
# Limits and homological algebra for linear right modules

We retain the existing definition of `ZAlgebra.RightModule`: additive,
`k`-linear presheaves on `A.Obj` with values in `ModuleCat k`.
The right action in the paper's §1.2 sends `M_v` to `M_u` along
`A.Hom u v = e_v A e_u`, hence has exactly this contravariant orientation.
-/

namespace ASGinzburg.ZAlgebra

open CategoryTheory CategoryTheory.Limits

universe u v w w'

variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- Any pointwise limit of linear right modules is again additive and linear. -/
theorem rightModuleProperty_closedUnderLimits
    (J : Type w) [Category.{w'} J] [HasLimitsOfShape J (ModuleCat.{v} k)] :
    ClosedUnderLimitsOfShape J A.rightModuleProperty := by
  intro F c hc hF
  constructor
  · constructor
    intro X Y f g
    apply (isLimitOfPreserves ((evaluation A.Objᵒᵖ (ModuleCat.{v} k)).obj Y) hc).hom_ext
    intro j
    letI := (hF j).1
    change c.pt.map (f + g) ≫ (c.π.app j).app Y =
      (c.pt.map f + c.pt.map g) ≫ (c.π.app j).app Y
    simp only [Preadditive.add_comp, NatTrans.naturality, Functor.map_add,
      Preadditive.comp_add]
  · constructor
    intro X Y f r
    apply (isLimitOfPreserves ((evaluation A.Objᵒᵖ (ModuleCat.{v} k)).obj Y) hc).hom_ext
    intro j
    letI := (hF j).2
    change c.pt.map (r • f) ≫ (c.π.app j).app Y =
      (r • c.pt.map f) ≫ (c.π.app j).app Y
    simp only [Linear.smul_comp, NatTrans.naturality, Functor.map_smul,
      Linear.comp_smul]

/-- Any pointwise colimit of linear right modules is again additive and linear. -/
theorem rightModuleProperty_closedUnderColimits
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J (ModuleCat.{v} k)] :
    ClosedUnderColimitsOfShape J A.rightModuleProperty := by
  intro F c hc hF
  constructor
  · constructor
    intro X Y f g
    apply (isColimitOfPreserves ((evaluation A.Objᵒᵖ (ModuleCat.{v} k)).obj X) hc).hom_ext
    intro j
    letI := (hF j).1
    change (c.ι.app j).app X ≫ c.pt.map (f + g) =
      (c.ι.app j).app X ≫ (c.pt.map f + c.pt.map g)
    erw [← (c.ι.app j).naturality (f + g), Functor.map_add, Preadditive.add_comp,
      (c.ι.app j).naturality f, (c.ι.app j).naturality g, Preadditive.comp_add]
    rfl
  · constructor
    intro X Y f r
    apply (isColimitOfPreserves ((evaluation A.Objᵒᵖ (ModuleCat.{v} k)).obj X) hc).hom_ext
    intro j
    letI := (hF j).2
    change (c.ι.app j).app X ≫ c.pt.map (r • f) =
      (c.ι.app j).app X ≫ (r • c.pt.map f)
    erw [← (c.ι.app j).naturality (r • f), Functor.map_smul, Linear.smul_comp,
      (c.ι.app j).naturality f, Linear.comp_smul]
    rfl

/-- Limits are inherited without leaving the category of linear right modules. -/
noncomputable instance rightModuleHasLimitsOfShape
    (J : Type w) [Category.{w'} J] [HasLimitsOfShape J (ModuleCat.{v} k)] :
    HasLimitsOfShape J A.RightModule :=
  hasLimitsOfShape_of_closedUnderLimits (A.rightModuleProperty_closedUnderLimits J)

/-- Colimits are inherited without leaving the category of linear right modules. -/
noncomputable instance rightModuleHasColimitsOfShape
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J (ModuleCat.{v} k)] :
    HasColimitsOfShape J A.RightModule :=
  hasColimitsOfShape_of_closedUnderColimits (A.rightModuleProperty_closedUnderColimits J)

/-- The full-subcategory inclusion creates limits in the ambient presheaf category. -/
noncomputable instance rightModuleInclusionCreatesLimitsOfShape
    (J : Type w) [Category.{w'} J] [HasLimitsOfShape J (ModuleCat.{v} k)] :
    CreatesLimitsOfShape J A.rightModuleProperty.ι :=
  createsLimitsOfShapeFullSubcategoryInclusion (A.rightModuleProperty_closedUnderLimits J)

/-- The full-subcategory inclusion creates colimits in the ambient presheaf category. -/
noncomputable instance rightModuleInclusionCreatesColimitsOfShape
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J (ModuleCat.{v} k)] :
    CreatesColimitsOfShape J A.rightModuleProperty.ι :=
  createsColimitsOfShapeFullSubcategoryInclusion (A.rightModuleProperty_closedUnderColimits J)

/-- In particular, right modules have the finite products needed for the Abelian criterion. -/
noncomputable instance rightModuleHasFiniteProducts : HasFiniteProducts A.RightModule where
  out _ := inferInstance

/-- Coimages and images agree: the inclusion preserves both constructions and reflects isos. -/
noncomputable instance rightModuleCoimageImageComparisonIsIso
    {M N : A.RightModule} (f : M ⟶ N) : IsIso (Abelian.coimageImageComparison f) := by
  haveI : IsIso (A.rightModuleProperty.ι.map (Abelian.coimageImageComparison f)) := by
    rw [Arrow.isIso_iff_isIso_of_isIso
      (Abelian.PreservesCoimageImageComparison.iso A.rightModuleProperty.ι f).hom]
    infer_instance
  exact isIso_of_reflects_iso _ A.rightModuleProperty.ι

/-- The existing category of additive, linear right presheaves is Abelian. -/
noncomputable instance rightModuleAbelian : Abelian A.RightModule :=
  Abelian.ofCoimageImageComparisonIsIso

/-- The inclusion preserves finite limits, in particular kernels. -/
noncomputable instance rightModuleInclusionPreservesFiniteLimits :
    PreservesFiniteLimits A.rightModuleProperty.ι where
  preservesFiniteLimits _ := inferInstance

/-- The inclusion preserves finite colimits, in particular cokernels. -/
noncomputable instance rightModuleInclusionPreservesFiniteColimits :
    PreservesFiniteColimits A.rightModuleProperty.ι where
  preservesFiniteColimits _ := inferInstance

end ASGinzburg.ZAlgebra
