import ASGinzburg.FoundationTotalFunctor

/-! The actual finite foundation total-module functor is additive and
faithful. Fullness and inverse reconstruction remain further proofs. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u
variable {k : Type u} [Field k] (A : ZAlgebra.{u,u} k) (Q : CutQuiver)

noncomputable instance foundationRightTotalFunctorAdditive :
    (A.foundationRightTotalFunctor Q).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    funext i
    rfl

noncomputable instance foundationRightTotalFunctorFaithful :
    (A.foundationRightTotalFunctor Q).Faithful where
  map_injective := by
    intro M N f g h
    apply NatTrans.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hh := congrArg (fun t => t (Pi.single i x) i) h
    simpa only [foundationRightTotalFunctor_map_apply,Pi.single_eq_same] using hh

end ASGinzburg.ZAlgebra
