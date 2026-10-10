import ASGinzburg.ZAlgebraRightModuleEquivalence
import ASGinzburg.RightModuleMinimality

/-! An explicit vertex-fixing module transport. Its component spaces are
literally the old component spaces; its action uses the inverse algebra map.
This supplies direct control of the genuine positive-action radical. -/
namespace ASGinzburg.ZAlgebra.Isomorphism
open CategoryTheory CategoryTheory.Functor Opposite
universe u v
variable {k : Type u} [Field k] {A B : ZAlgebra.{u,v} k}
variable (E : Isomorphism A B)

noncomputable def fixedRightModuleFunctor : A.RightModule ⥤ B.RightModule where
  obj M := by
    letI : M.obj.Additive := M.property.1
    letI : M.obj.Linear k := M.property.2
    letI : E.symm.linearFunctor.op.Additive := E.symm.linearEquivalenceOpFunctorAdditive
    letI : E.symm.linearFunctor.op.Linear k := E.symm.linearEquivalenceOpFunctorLinear
    exact ⟨E.symm.linearFunctor.op ⋙ M.obj,⟨inferInstance,inferInstance⟩⟩
  map f := whiskerLeft E.symm.linearFunctor.op f
  map_id _ := rfl
  map_comp _ _ := rfl

instance fixedRightModuleFunctorAdditive : E.fixedRightModuleFunctor.Additive where
  map_add := by intro M N f g; rfl

instance fixedRightModuleFunctorLinear : E.fixedRightModuleFunctor.Linear k where
  map_smul := by intro M N f c; rfl

theorem fixedRightModuleFunctor_positiveActionSpan (M : A.RightModule) (i : ℤ) :
    B.positiveActionSpan (E.fixedRightModuleFunctor.obj M) i=A.positiveActionSpan M i := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨l,hil,x,a,rfl⟩
    exact Submodule.subset_span ⟨l,hil,x,(E.map i l).symm a,rfl⟩
  · apply Submodule.span_le.mpr
    rintro y ⟨l,hil,x,a,rfl⟩
    apply Submodule.subset_span
    refine ⟨l,hil,x,E.map i l a,?_⟩
    change M.obj.map ((show (⟨i⟩:A.Obj)⟶⟨l⟩ from
      (E.map i l).symm (E.map i l a)).op) x=
        M.obj.map ((show (⟨i⟩:A.Obj)⟶⟨l⟩ from a).op) x
    rw [LinearEquiv.symm_apply_apply]

theorem fixedRightModuleFunctor_minimal {M N : A.RightModule} (f : M⟶N)
    (hf : A.IsMinimalMorphism f) : B.IsMinimalMorphism (E.fixedRightModuleFunctor.map f) := by
  intro i x
  rw [E.fixedRightModuleFunctor_positiveActionSpan]
  exact hf i x

end ASGinzburg.ZAlgebra.Isomorphism
