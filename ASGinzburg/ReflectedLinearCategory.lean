import ASGinzburg.ReflectedZAlgebra
import ASGinzburg.LeftModules

/-! The reflected algebra's actual linear category is equivalent to
the opposite of the original linear category. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

def reflectedLinearFunctor (c : ℤ) : (A.reflected c).Obj ⥤ A.Objᵒᵖ where
  obj X := op ⟨c-X.index⟩
  map f := Quiver.Hom.op f
  map_id _ := rfl
  map_comp _ _ := rfl

instance reflectedLinearFunctorAdditive (c : ℤ) : (A.reflectedLinearFunctor c).Additive where
  map_add := by intro X Y f g; rfl

instance reflectedLinearFunctorLinear (c : ℤ) : (A.reflectedLinearFunctor c).Linear k where
  map_smul := by intro X Y f r; rfl

instance reflectedLinearFunctorFaithful (c : ℤ) : (A.reflectedLinearFunctor c).Faithful where
  map_injective h := congrArg Quiver.Hom.unop h

instance reflectedLinearFunctorFull (c : ℤ) : (A.reflectedLinearFunctor c).Full where
  map_surjective f := ⟨f.unop, rfl⟩

instance reflectedLinearFunctorEssSurj (c : ℤ) : (A.reflectedLinearFunctor c).EssSurj where
  mem_essImage Y := by
    refine ⟨⟨c-Y.unop.index⟩, ?_⟩
    have he : (A.reflectedLinearFunctor c).obj ⟨c-Y.unop.index⟩ = Y := by
      apply Opposite.unop_injective
      change (⟨c-(c-Y.unop.index)⟩ : A.Obj) = Y.unop
      cases Y with
      | op Y =>
        cases Y with
        | mk i =>
          change (⟨c-(c-i)⟩ : A.Obj) = ⟨i⟩
          congr 1
          omega
    exact ⟨eqToIso he⟩

instance reflectedLinearFunctorIsEquivalence (c : ℤ) :
    (A.reflectedLinearFunctor c).IsEquivalence where

noncomputable def reflectedLinearEquivalence (c : ℤ) :
    (A.reflected c).Obj ≌ A.Objᵒᵖ :=
  (A.reflectedLinearFunctor c).asEquivalence

end ASGinzburg.ZAlgebra
