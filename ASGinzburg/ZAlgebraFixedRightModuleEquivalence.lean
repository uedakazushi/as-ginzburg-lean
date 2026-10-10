import ASGinzburg.ZAlgebraFixedRightModuleFunctor

/-! The explicit transport is an actual equivalence, with componentwise
identity unit/counit whose action compatibility is inverse-map cancellation. -/
namespace ASGinzburg.ZAlgebra.Isomorphism
open CategoryTheory CategoryTheory.Functor Opposite
universe u v
variable {k : Type u} [Field k] {A B : ZAlgebra.{u,v} k}
variable (E : Isomorphism A B)

noncomputable def fixedRightModuleUnitIso :
    𝟭 A.RightModule ≅ E.fixedRightModuleFunctor ⋙ E.symm.fixedRightModuleFunctor :=
  NatIso.ofComponents (fun M => ObjectProperty.isoMk _
    (NatIso.ofComponents (fun X => Iso.refl (M.obj.obj X)) (by
      intro X Y f
      change M.obj.map f=M.obj.map ((show Y.unop⟶X.unop from
        (E.map Y.unop.index X.unop.index).symm
          (E.map Y.unop.index X.unop.index f.unop)).op)
      rw [LinearEquiv.symm_apply_apply]
      simp))) (by
    intro M N f
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    rfl)

noncomputable def fixedRightModuleEquivalence : A.RightModule ≌ B.RightModule :=
  CategoryTheory.Equivalence.mk E.fixedRightModuleFunctor E.symm.fixedRightModuleFunctor
    E.fixedRightModuleUnitIso E.symm.fixedRightModuleUnitIso.symm

instance fixedRightModuleFunctorIsEquivalence : E.fixedRightModuleFunctor.IsEquivalence :=
  E.fixedRightModuleEquivalence.isEquivalence_functor

end ASGinzburg.ZAlgebra.Isomorphism
