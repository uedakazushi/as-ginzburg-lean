import ASGinzburg.LeftModules

/-! Precomposition by an additive linear equivalence preserves the actual
full subcategories of additive linear module-valued functors. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Functor
universe u v v' w w' z
variable (k : Type u) [Field k]
variable (C : Type v) [Category.{v'} C] [Preadditive C] [Linear k C]

def linearModuleFunctorProperty : ObjectProperty (C ⥤ ModuleCat.{z} k) :=
  fun F => F.Additive ∧ F.Linear k

variable {k C} {D : Type w} [Category.{w'} D] [Preadditive D] [Linear k D]
variable (E : C ≌ D) [E.functor.Linear k] [E.functor.Additive]

noncomputable def linearRepresentationPrecomposition :
    (linearModuleFunctorProperty k C).FullSubcategory ⥤
      (linearModuleFunctorProperty k D).FullSubcategory where
  obj M := by
    letI : M.obj.Additive := M.property.1
    letI : M.obj.Linear k := M.property.2
    exact ⟨E.inverse ⋙ M.obj, ⟨inferInstance, inferInstance⟩⟩
  map f := whiskerLeft E.inverse f
  map_id _ := rfl
  map_comp _ _ := rfl

instance linearRepresentationPrecompositionAdditive :
    (linearRepresentationPrecomposition (k := k) E).Additive where
  map_add := by intro M N f g; rfl

instance linearRepresentationPrecompositionLinear :
    (linearRepresentationPrecomposition (k := k) E).Linear k where
  map_smul := by intro M N f r; rfl

instance linearRepresentationPrecompositionFaithful :
    (linearRepresentationPrecomposition (k := k) E).Faithful where
  map_injective := by
    intro M N f g h
    exact (Equivalence.congrLeft E).functor.map_injective h

instance linearRepresentationPrecompositionFull :
    (linearRepresentationPrecomposition (k := k) E).Full where
  map_surjective := by
    intro M N f
    exact (Equivalence.congrLeft E).functor.map_surjective f

instance linearRepresentationPrecompositionEssSurj :
    (linearRepresentationPrecomposition (k := k) E).EssSurj where
  mem_essImage M := by
    letI : M.obj.Additive := M.property.1
    letI : M.obj.Linear k := M.property.2
    let N : (linearModuleFunctorProperty k C).FullSubcategory :=
      ⟨E.functor ⋙ M.obj, ⟨inferInstance, inferInstance⟩⟩
    refine ⟨N, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _ ((Equivalence.congrLeft E).counitIso.app M.obj)

instance linearRepresentationPrecompositionIsEquivalence :
    (linearRepresentationPrecomposition (k := k) E).IsEquivalence where

noncomputable def linearRepresentationEquivalence :
    (linearModuleFunctorProperty k C).FullSubcategory ≌
      (linearModuleFunctorProperty k D).FullSubcategory :=
  (linearRepresentationPrecomposition (k := k) E).asEquivalence

end ASGinzburg
