import ASGinzburg.FiniteDimensionalExtDuality

namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v w w'
variable {C : Type u} [Category.{v} C] {J : Type w} [Category.{w'} J]

theorem limitConeProductMono {F : J ⥤ C} (c : Cone F) (hc : IsLimit c)
    [HasProduct (fun j => F.obj j)] : Mono (Pi.lift (fun j => c.π.app j)) := by
  constructor
  intro X f g h
  apply hc.hom_ext
  intro j
  have H := congrArg (fun t => t ≫ Pi.π (fun j => F.obj j) j) h
  simpa only [Category.assoc,Pi.lift_π] using H

theorem colimitCoconeCoproductEpi {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c)
    [HasCoproduct (fun j => F.obj j)] : Epi (Sigma.desc (fun j => c.ι.app j)) := by
  constructor
  intro X f g h
  apply hc.hom_ext
  intro j
  have H := congrArg (fun t => Sigma.ι (fun j => F.obj j) j ≫ t) h
  simpa only [← Category.assoc,Sigma.ι_desc] using H
end ASGinzburg

