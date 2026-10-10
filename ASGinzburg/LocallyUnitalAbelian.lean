import ASGinzburg.LocallyUnitalEquivalence
import Mathlib.CategoryTheory.Abelian.Transfer
import ASGinzburg.LeftModuleExt

/-! The proved equivalences are additive and k-linear. Transported finite
products and enough projectives make the concrete locally unital module
categories Abelian and give actual derived-category Ext in the Hom universe. -/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ModuleCat.Algebra DirectSum
attribute [local instance 2000] ModuleCat.isModule
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

instance leftTotalLocallyUnitalFunctorAdditive : A.leftTotalLocallyUnitalFunctor.Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro i
    rfl

instance rightTotalLocallyUnitalFunctorAdditive : A.rightTotalLocallyUnitalFunctor.Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro i
    rfl

instance leftLocallyUnitalComponentFunctorAdditive : A.leftLocallyUnitalComponentFunctor.Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl

instance rightLocallyUnitalComponentFunctorAdditive : A.rightLocallyUnitalComponentFunctor.Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl

instance leftTotalLocallyUnitalFunctorLinear : A.leftTotalLocallyUnitalFunctor.Linear k where
  map_smul := by
    intro M N f r
    letI := A.leftTotalUnitizationModule N
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change A.leftTotalLinearMap (r • f) x =
      A.leftTotalUnitalRepresentation N (algebraMap k A.totalUnitization r) (A.leftTotalLinearMap f x)
    rw [A.leftTotalUnitalRepresentation_algebraMap_apply]
    apply DFinsupp.ext
    intro i
    rfl

instance rightTotalLocallyUnitalFunctorLinear : A.rightTotalLocallyUnitalFunctor.Linear k where
  map_smul := by
    intro M N f r
    letI := A.rightTotalUnitizationModule N
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change A.rightTotalLinearMap (r • f) x =
      A.rightTotalUnitalRepresentation N (algebraMap k A.totalUnitizationᵐᵒᵖ r) (A.rightTotalLinearMap f x)
    rw [A.rightTotalUnitalRepresentation_algebraMap_apply]
    apply DFinsupp.ext
    intro i
    rfl

instance leftLocallyUnitalComponentFunctorLinear : A.leftLocallyUnitalComponentFunctor.Linear k where
  map_smul := by
    intro M N f r
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl

instance rightLocallyUnitalComponentFunctorLinear : A.rightLocallyUnitalComponentFunctor.Linear k where
  map_smul := by
    intro M N f r
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl

instance leftLocallyUnitalComponentFunctorIsEquivalence : A.leftLocallyUnitalComponentFunctor.IsEquivalence :=
  A.leftLocallyUnitalEquivalence.isEquivalence_inverse

instance rightLocallyUnitalComponentFunctorIsEquivalence : A.rightLocallyUnitalComponentFunctor.IsEquivalence :=
  A.rightLocallyUnitalEquivalence.isEquivalence_inverse

noncomputable instance leftLocallyUnitalHasFiniteProducts : HasFiniteProducts A.LeftLocallyUnitalModule :=
  ⟨fun n => by
    letI : HasLimitsOfShape (Discrete (Fin n)) A.LeftModule := A.leftModuleHasFiniteProducts.out n
    exact Adjunction.hasLimitsOfShape_of_equivalence (J := Discrete (Fin n)) A.leftLocallyUnitalComponentFunctor⟩

noncomputable instance rightLocallyUnitalHasFiniteProducts : HasFiniteProducts A.RightLocallyUnitalModule :=
  ⟨fun n => by
    letI : HasLimitsOfShape (Discrete (Fin n)) A.RightModule := A.rightModuleHasFiniteProducts.out n
    exact Adjunction.hasLimitsOfShape_of_equivalence (J := Discrete (Fin n)) A.rightLocallyUnitalComponentFunctor⟩

noncomputable instance leftLocallyUnitalAbelian : Abelian A.LeftLocallyUnitalModule :=
  abelianOfEquivalence A.leftLocallyUnitalComponentFunctor

noncomputable instance rightLocallyUnitalAbelian : Abelian A.RightLocallyUnitalModule :=
  abelianOfEquivalence A.rightLocallyUnitalComponentFunctor

instance leftLocallyUnitalEnoughProjectives : EnoughProjectives A.LeftLocallyUnitalModule :=
  A.leftLocallyUnitalEquivalence.enoughProjectives_iff.mp inferInstance

instance rightLocallyUnitalEnoughProjectives : EnoughProjectives A.RightLocallyUnitalModule :=
  A.rightLocallyUnitalEquivalence.enoughProjectives_iff.mp inferInstance

instance leftLocallyUnitalHasExt : HasExt.{v} A.LeftLocallyUnitalModule :=
  hasExt_of_enoughProjectives A.LeftLocallyUnitalModule

instance rightLocallyUnitalHasExt : HasExt.{v} A.RightLocallyUnitalModule :=
  hasExt_of_enoughProjectives A.RightLocallyUnitalModule

end ASGinzburg.ZAlgebra
