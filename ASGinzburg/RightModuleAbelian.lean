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

end ASGinzburg.ZAlgebra
