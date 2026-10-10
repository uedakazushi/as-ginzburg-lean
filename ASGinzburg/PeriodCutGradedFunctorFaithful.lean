import ASGinzburg.PeriodCutGradedFunctorLinear

/-! The actual cut graded-module functor detects all cover-module morphisms. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cornerCoordinateObject_surjective : Function.Surjective (E.cornerCoordinateObject Q) := by
  intro X
  exact ⟨Q.heightEquiv.symm X.index,by
    cases X
    simp only [cornerCoordinateObject,Equiv.apply_symm_apply]⟩

instance cornerGradedModuleFunctorFaithful : (E.cornerGradedModuleFunctor Q).Faithful where
  map_injective := by
    intro M N f g h
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    cases X using Opposite.rec
    rename_i X
    obtain ⟨x,rfl⟩ := E.cornerCoordinateObject_surjective Q X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    have he := congrArg (fun t => t.val (DirectSum.lof k Q.LiftVertex
      (E.CornerModuleSpace Q M) x v)) h
    change E.cornerTotalModuleLinearMap Q f (DirectSum.lof k Q.LiftVertex _ x v)=
      E.cornerTotalModuleLinearMap Q g (DirectSum.lof k Q.LiftVertex _ x v) at he
    rw [E.cornerTotalModuleLinearMap_lof,E.cornerTotalModuleLinearMap_lof] at he
    simpa only [DirectSum.lof_apply] using congrArg (fun z => z x) he

end ASGinzburg.ZAlgebra.PeriodIso
