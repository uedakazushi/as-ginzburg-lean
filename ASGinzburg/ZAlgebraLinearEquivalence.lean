import ASGinzburg.ZAlgebraIsomorphisms
import ASGinzburg.LeftModules

/-! Vertex-fixing actual algebra isomorphisms give additive k-linear
equivalences of the original, concrete linear categories. -/
namespace ASGinzburg.ZAlgebra.Isomorphism
open CategoryTheory
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {B : ZAlgebra.{u,w} k}

noncomputable def linearFunctor (E : Isomorphism A B) : A.Obj ⥤ B.Obj where
  obj X := ⟨X.index⟩
  map f := E.map _ _ f
  map_id X := E.map_id X.index
  map_comp f g := E.map_comp f g

instance linearFunctorAdditive (E : Isomorphism A B) : E.linearFunctor.Additive where
  map_add := by intro X Y f g; exact (E.map X.index Y.index).map_add f g

instance linearFunctorLinear (E : Isomorphism A B) : E.linearFunctor.Linear k where
  map_smul := by intro X Y f r; exact (E.map X.index Y.index).map_smul r f

instance linearFunctorFaithful (E : Isomorphism A B) : E.linearFunctor.Faithful where
  map_injective := by
    intro X Y f g h
    exact (E.map X.index Y.index).injective h

instance linearFunctorFull (E : Isomorphism A B) : E.linearFunctor.Full where
  map_surjective := (E.map _ _).surjective

instance linearFunctorEssSurj (E : Isomorphism A B) : E.linearFunctor.EssSurj where
  mem_essImage Y := by
    refine ⟨⟨Y.index⟩, ?_⟩
    cases Y
    exact ⟨Iso.refl _⟩

instance linearFunctorIsEquivalence (E : Isomorphism A B) : E.linearFunctor.IsEquivalence where

noncomputable def linearEquivalence (E : Isomorphism A B) : A.Obj ≌ B.Obj :=
  E.linearFunctor.asEquivalence

end ASGinzburg.ZAlgebra.Isomorphism
