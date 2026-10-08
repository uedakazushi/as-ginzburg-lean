import ASGinzburg.LeftModules
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-!
# Abelian structure of concrete linear left modules

Pointwise limits and colimits preserve additive k-linear covariance.
The full-subcategory inclusion creates them, so the existing left modules
are Abelian and support actual kernels, quotients, and homology.
-/

namespace ASGinzburg.ZAlgebra

open CategoryTheory CategoryTheory.Limits

universe u v w w'

variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- Any pointwise limit of linear left modules is again additive and linear. -/
theorem leftModuleProperty_closedUnderLimits
    (J : Type w) [Category.{w'} J] [HasLimitsOfShape J (ModuleCat.{v} k)] :
    ClosedUnderLimitsOfShape J A.leftModuleProperty := by
  intro F c hc hF
  constructor
  · constructor
    intro X Y f g
    apply (isLimitOfPreserves ((evaluation A.Obj (ModuleCat.{v} k)).obj Y) hc).hom_ext
    intro j
    letI := (hF j).1
    change c.pt.map (f + g) ≫ (c.π.app j).app Y =
      (c.pt.map f + c.pt.map g) ≫ (c.π.app j).app Y
    simp only [Preadditive.add_comp, NatTrans.naturality, Functor.map_add,
      Preadditive.comp_add]
  · constructor
    intro X Y f r
    apply (isLimitOfPreserves ((evaluation A.Obj (ModuleCat.{v} k)).obj Y) hc).hom_ext
    intro j
    letI := (hF j).2
    change c.pt.map (r • f) ≫ (c.π.app j).app Y =
      (r • c.pt.map f) ≫ (c.π.app j).app Y
    simp only [Linear.smul_comp, NatTrans.naturality, Functor.map_smul,
      Linear.comp_smul]

/-- Any pointwise colimit of linear left modules is again additive and linear. -/
theorem leftModuleProperty_closedUnderColimits
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J (ModuleCat.{v} k)] :
    ClosedUnderColimitsOfShape J A.leftModuleProperty := by
  intro F c hc hF
  constructor
  · constructor
    intro X Y f g
    apply (isColimitOfPreserves ((evaluation A.Obj (ModuleCat.{v} k)).obj X) hc).hom_ext
    intro j
    letI := (hF j).1
    change (c.ι.app j).app X ≫ c.pt.map (f + g) =
      (c.ι.app j).app X ≫ (c.pt.map f + c.pt.map g)
    erw [← (c.ι.app j).naturality (f + g), Functor.map_add, Preadditive.add_comp,
      (c.ι.app j).naturality f, (c.ι.app j).naturality g, Preadditive.comp_add]
    rfl
  · constructor
    intro X Y f r
    apply (isColimitOfPreserves ((evaluation A.Obj (ModuleCat.{v} k)).obj X) hc).hom_ext
    intro j
    letI := (hF j).2
    change (c.ι.app j).app X ≫ c.pt.map (r • f) =
      (c.ι.app j).app X ≫ (r • c.pt.map f)
    erw [← (c.ι.app j).naturality (r • f), Functor.map_smul, Linear.smul_comp,
      (c.ι.app j).naturality f, Linear.comp_smul]
    rfl

/-- Limits are inherited without leaving the category of linear left modules. -/
noncomputable instance leftModuleHasLimitsOfShape
    (J : Type w) [Category.{w'} J] [HasLimitsOfShape J (ModuleCat.{v} k)] :
    HasLimitsOfShape J A.LeftModule :=
  hasLimitsOfShape_of_closedUnderLimits (A.leftModuleProperty_closedUnderLimits J)

/-- Colimits are inherited without leaving the category of linear left modules. -/
noncomputable instance leftModuleHasColimitsOfShape
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J (ModuleCat.{v} k)] :
    HasColimitsOfShape J A.LeftModule :=
  hasColimitsOfShape_of_closedUnderColimits (A.leftModuleProperty_closedUnderColimits J)

/-- The full-subcategory inclusion creates limits in the ambient presheaf category. -/
noncomputable instance leftModuleInclusionCreatesLimitsOfShape
    (J : Type w) [Category.{w'} J] [HasLimitsOfShape J (ModuleCat.{v} k)] :
    CreatesLimitsOfShape J A.leftModuleProperty.ι :=
  createsLimitsOfShapeFullSubcategoryInclusion (A.leftModuleProperty_closedUnderLimits J)

/-- The full-subcategory inclusion creates colimits in the ambient presheaf category. -/
noncomputable instance leftModuleInclusionCreatesColimitsOfShape
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J (ModuleCat.{v} k)] :
    CreatesColimitsOfShape J A.leftModuleProperty.ι :=
  createsColimitsOfShapeFullSubcategoryInclusion (A.leftModuleProperty_closedUnderColimits J)

/-- In particular, left modules have the finite products needed for the Abelian criterion. -/
noncomputable instance leftModuleHasFiniteProducts : HasFiniteProducts A.LeftModule where
  out _ := inferInstance

/-- Coimages and images agree: the inclusion preserves both constructions and reflects isos. -/
noncomputable instance leftModuleCoimageImageComparisonIsIso
    {M N : A.LeftModule} (f : M ⟶ N) : IsIso (Abelian.coimageImageComparison f) := by
  haveI : IsIso (A.leftModuleProperty.ι.map (Abelian.coimageImageComparison f)) := by
    rw [Arrow.isIso_iff_isIso_of_isIso
      (Abelian.PreservesCoimageImageComparison.iso A.leftModuleProperty.ι f).hom]
    infer_instance
  exact isIso_of_reflects_iso _ A.leftModuleProperty.ι

/-- The existing category of additive, linear left presheaves is Abelian. -/
noncomputable instance leftModuleAbelian : Abelian A.LeftModule :=
  Abelian.ofCoimageImageComparisonIsIso

/-- The inclusion preserves finite limits, in particular kernels. -/
noncomputable instance leftModuleInclusionPreservesFiniteLimits :
    PreservesFiniteLimits A.leftModuleProperty.ι where
  preservesFiniteLimits _ := inferInstance

/-- The inclusion preserves finite colimits, in particular cokernels. -/
noncomputable instance leftModuleInclusionPreservesFiniteColimits :
    PreservesFiniteColimits A.leftModuleProperty.ι where
  preservesFiniteColimits _ := inferInstance

end ASGinzburg.ZAlgebra
