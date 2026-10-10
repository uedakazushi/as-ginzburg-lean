import ASGinzburg.FoundationTotalModules
import ASGinzburg.FoundationTotalMaps

/-! The original foundation linear presheaf category maps functorially
to genuine modules over the finite opposite convolution algebra. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u
variable {k : Type u} [Field k] (A : ZAlgebra.{u,u} k) (Q : CutQuiver)

noncomputable def foundationRightTotalModuleMap {M N : A.FoundationRightModule Q}
    (f : M ⟶ N) : A.foundationRightTotalModule Q M ⟶ A.foundationRightTotalModule Q N := by
  letI := A.foundationRightTotalModuleStructure Q M
  letI := A.foundationRightTotalModuleStructure Q N
  exact ModuleCat.ofHom {
    toFun := A.foundationRightTotalLinearMap Q f
    map_add' := (A.foundationRightTotalLinearMap Q f).map_add
    map_smul' := by
      intro r m
      change A.foundationRightTotalLinearMap Q f (A.foundationRightTotalAction Q M r.unop m)=
        A.foundationRightTotalAction Q N r.unop (A.foundationRightTotalLinearMap Q f m)
      exact LinearMap.congr_fun (A.foundationRightTotalLinearMap_action Q f r.unop) m }

noncomputable def foundationRightTotalFunctor :
    A.FoundationRightModule Q ⥤ ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ where
  obj := A.foundationRightTotalModule Q
  map := A.foundationRightTotalModuleMap Q
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    funext i
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    funext i
    rfl

theorem foundationRightTotalFunctor_map_apply {M N : A.FoundationRightModule Q}
    (f : M ⟶ N) (m : A.foundationRightTotalModule Q M) (i : Q.Vertex) :
    (A.foundationRightTotalFunctor Q).map f m i=(f.hom.app i).hom (m i) := rfl

end ASGinzburg.ZAlgebra
