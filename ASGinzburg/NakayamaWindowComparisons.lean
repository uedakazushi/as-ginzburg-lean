import ASGinzburg.NakayamaWindowProjectives

/-! Comparison of the restricted Nakayama functor and simple isomorphisms
with their underlying finite-dimensional module data. -/
namespace ASGinzburg
open CategoryTheory
universe u v u' v'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
theorem equivalenceMk_functor_eq (F : C ⥤ D) (G : D ⥤ C)
    (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) :
    (CategoryTheory.Equivalence.mk F G η ε).functor = F := rfl
end ASGinzburg

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
theorem rightFiniteWindowNakayamaEquivalence_functor_eq (hAS : A.ASRegular Q) (l r : ℤ) :
    (A.rightFiniteWindowNakayamaEquivalence Q hAS l r).functor =
      A.rightFiniteWindowNakayamaFunctor Q hAS l r :=
  ASGinzburg.equivalenceMk_functor_eq _ _ _ _
end ASGinzburg.ZAlgebra


namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def rightFiniteWindowNakayamaSimpleIsoWith (hAS : A.ASRegular Q)
    (l r i : ℤ) (hli : l ≤ i) (hir : i ≤ r)
    (γ : (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor.obj
      (A.rightFiniteDimensionalSimple i) ≅ A.rightFiniteDimensionalSimple (i-Q.vertices)) :
    (A.rightFiniteWindowNakayamaEquivalence Q hAS l r).functor.obj
      (A.rightFiniteWindowSimple l r i hli hir) ≅
        A.rightFiniteWindowSimple (l-Q.vertices) (r-Q.vertices) (i-Q.vertices)
          (sub_le_sub_right hli _) (sub_le_sub_right hir _) :=
  (A.rightFiniteWindowProperty (l-Q.vertices) (r-Q.vertices)).isoMk γ

theorem rightFiniteWindowNakayamaSimpleIsoWith_underlying_hom (hAS : A.ASRegular Q)
    (l r i : ℤ) (hli : l ≤ i) (hir : i ≤ r)
    (γ : (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor.obj
      (A.rightFiniteDimensionalSimple i) ≅ A.rightFiniteDimensionalSimple (i-Q.vertices)) :
    A.rightFiniteDimensionalProperty.ι.map
        ((A.rightFiniteWindowProperty (l-Q.vertices) (r-Q.vertices)).ι.map
          (A.rightFiniteWindowNakayamaSimpleIsoWith Q hAS l r i hli hir γ).hom) =
      A.rightFiniteDimensionalProperty.ι.map γ.hom := rfl

theorem rightFiniteWindowNakayamaSimpleIso_underlying_hom (hAS : A.ASRegular Q)
    (l r i : ℤ) (hli : l ≤ i) (hir : i ≤ r) :
    A.rightFiniteDimensionalProperty.ι.map
        ((A.rightFiniteWindowProperty (l-Q.vertices) (r-Q.vertices)).ι.map
          (A.rightFiniteWindowNakayamaSimpleIso Q hAS l r i hli hir).hom) =
      A.rightFiniteDimensionalProperty.ι.map
        (A.rightFiniteDimensionalNakayamaSimpleHeightIso Q hAS i).hom :=
  A.rightFiniteWindowNakayamaSimpleIsoWith_underlying_hom Q hAS l r i hli hir
    (A.rightFiniteDimensionalNakayamaSimpleHeightIso Q hAS i)
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
theorem rightFiniteWindowNakayamaFunctor_underlying_map (hAS : A.ASRegular Q)
    (l r : ℤ) {M N : A.RightFiniteWindow l r} (f : M ⟶ N) :
    A.rightFiniteDimensionalProperty.ι.map
        ((A.rightFiniteWindowProperty (l-Q.vertices) (r-Q.vertices)).ι.map
          ((A.rightFiniteWindowNakayamaEquivalence Q hAS l r).functor.map f)) =
      A.rightFiniteDimensionalProperty.ι.map
        ((A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor.map
          ((A.rightFiniteWindowProperty l r).ι.map f)) := by
  dsimp only [rightFiniteWindowNakayamaEquivalence,CategoryTheory.Equivalence.mk,
    rightFiniteWindowNakayamaFunctor]
  rw [CategoryTheory.ObjectProperty.ι_obj_lift_map,CategoryTheory.Functor.comp_map]

end ASGinzburg.ZAlgebra
