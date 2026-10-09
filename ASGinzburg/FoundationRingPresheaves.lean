import ASGinzburg.FoundationRingComponentSpaces
import ASGinzburg.FoundationRightRestriction

/-! Every genuine finite opposite foundation-ring module recovers an
object of the existing additive linear foundation presheaf category. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
attribute [local instance 2000] ModuleCat.isModule
universe u
variable {k : Type u} [Field k] (A : ZAlgebra.{u,u} k) (Q : CutQuiver)

noncomputable def foundationRingRightComponentFunctor
    (M : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) :
    A.FoundationRightObj Q ⥤ ModuleCat.{u} k where
  obj i := ModuleCat.of k (A.foundationRingRightComponentSpace Q M i)
  map a := ModuleCat.ofHom (A.foundationRingRightComponentMap Q M a.unop)
  map_id i := by
    apply ModuleCat.hom_ext
    exact A.foundationRingRightComponentMap_id Q M i
  map_comp a b := by
    apply ModuleCat.hom_ext
    exact (A.foundationRingRightComponentMap_comp Q M b.unop a.unop).symm

noncomputable instance foundationRingRightComponentFunctorAdditive
    (M : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) :
    (A.foundationRingRightComponentFunctor Q M).Additive where
  map_add := by
    intro i j a b
    apply ModuleCat.hom_ext
    exact (A.foundationRingRightRangeActionLinear Q M j i).map_add a.unop b.unop

noncomputable instance foundationRingRightComponentFunctorLinear
    (M : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) :
    (A.foundationRingRightComponentFunctor Q M).Linear k where
  map_smul := by
    intro i j a c
    apply ModuleCat.hom_ext
    exact (A.foundationRingRightRangeActionLinear Q M j i).map_smul c a.unop

noncomputable def foundationRingRightComponentModule
    (M : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) : A.FoundationRightModule Q :=
  ⟨A.foundationRingRightComponentFunctor Q M,⟨inferInstance,inferInstance⟩⟩

end ASGinzburg.ZAlgebra
