import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! The ordinary tensor bifunctor with independently sized module
categories, needed for underlying vector-space tensor resolutions. -/
namespace ASGinzburg
open CategoryTheory
open scoped TensorProduct
universe u v w
variable (k : Type u) [CommRing k]

noncomputable def moduleTensorFunctor (M : ModuleCat.{v} k) :
    ModuleCat.{w} k ⥤ ModuleCat.{max v w} k where
  obj N := ModuleCat.of k (M ⊗[k] N)
  map f := ModuleCat.ofHom (TensorProduct.map LinearMap.id f.hom)
  map_id N := by
    apply ModuleCat.hom_ext
    exact TensorProduct.map_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext m n
    rfl

instance moduleTensorFunctor_additive (M : ModuleCat.{v} k) :
    (moduleTensorFunctor.{u, v, w} k M).Additive where
  map_add {X Y f g} := by
    apply ModuleCat.hom_ext
    exact TensorProduct.map_add_right _ _ _

noncomputable def moduleTensorBifunctor :
    ModuleCat.{v} k ⥤ ModuleCat.{w} k ⥤ ModuleCat.{max v w} k where
  obj := moduleTensorFunctor k
  map f :=
    { app N := ModuleCat.ofHom (TensorProduct.map f.hom LinearMap.id)
      naturality {N N'} g := by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        ext m n
        rfl }
  map_id M := by
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    exact TensorProduct.map_id
  map_comp f g := by
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext m n
    rfl

instance moduleTensorBifunctor_obj_additive (M : ModuleCat.{v} k) :
    ((moduleTensorBifunctor.{u, v, w} k).obj M).Additive :=
  moduleTensorFunctor_additive k M

instance moduleTensorBifunctor_additive :
    (moduleTensorBifunctor.{u, v, w} k).Additive where
  map_add {X Y f g} := by
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    exact TensorProduct.map_add_left _ _ _

end ASGinzburg
