import ASGinzburg.PeriodCutGradedModuleAbelian

/-! Forgetting the integer grading gives actual unital right R modules
and genuine R-linear maps. The resulting functor is additive. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cutGradedForgetFunctor : E.CutGradedRightModule Q ⥤
    ModuleCat.{v} (E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)))ᵐᵒᵖ where
  obj M := M.ringModule
  map {M N} f := ModuleCat.ofHom
    { toFun := f.val
      map_add' := f.val.map_add
      map_smul' := by
        intro r x
        exact f.property.1 r.unop x }
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

instance cutGradedForgetFunctorAdditive : (E.cutGradedForgetFunctor Q).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

noncomputable def cornerModuleRingFunctor : (E.cornerCoverZAlgebra Q).RightModule ⥤
    ModuleCat.{v} (E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)))ᵐᵒᵖ :=
  E.cornerGradedModuleFunctor Q ⋙ E.cutGradedForgetFunctor Q

instance cornerModuleRingFunctorAdditive : (E.cornerModuleRingFunctor Q).Additive := by
  change (E.cornerGradedModuleFunctor Q ⋙ E.cutGradedForgetFunctor Q).Additive
  infer_instance

end ASGinzburg.ZAlgebra.PeriodIso
