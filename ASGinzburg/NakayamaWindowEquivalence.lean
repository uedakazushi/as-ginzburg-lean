import ASGinzburg.NakayamaInverseWindowSupport

/-!
# The exact linear Nakayama equivalence restricted to finite intervals
-/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def rightFiniteWindowNakayamaFunctor (hAS : A.ASRegular Q) (l r : ℤ) :
    A.RightFiniteWindow l r ⥤ A.RightFiniteWindow (l-Q.vertices) (r-Q.vertices) :=
  (A.rightFiniteWindowProperty (l-Q.vertices) (r-Q.vertices)).lift
    ((A.rightFiniteWindowProperty l r).ι ⋙ (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor)
    (fun M => A.rightFiniteDimensional_nakayama_window Q hAS M.obj.obj M.obj.property l r M.property)

noncomputable def rightFiniteWindowNakayamaInverseFunctor (hAS : A.ASRegular Q) (l r : ℤ) :
    A.RightFiniteWindow (l-Q.vertices) (r-Q.vertices) ⥤ A.RightFiniteWindow l r :=
  (A.rightFiniteWindowProperty l r).lift
    ((A.rightFiniteWindowProperty (l-Q.vertices) (r-Q.vertices)).ι ⋙
      (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).inverse)
    (fun M => by
      have H := A.rightFiniteDimensional_nakayama_inverse_window Q hAS
        M.obj.obj M.obj.property (l-Q.vertices) (r-Q.vertices) M.property
      simpa only [sub_add_cancel] using H)

noncomputable def rightFiniteWindowNakayamaUnitIso (hAS : A.ASRegular Q) (l r : ℤ) :
    𝟭 (A.RightFiniteWindow l r) ≅
      A.rightFiniteWindowNakayamaFunctor Q hAS l r ⋙ A.rightFiniteWindowNakayamaInverseFunctor Q hAS l r :=
  NatIso.ofComponents (fun M => (A.rightFiniteWindowProperty l r).isoMk
    (X := M) (Y := (A.rightFiniteWindowNakayamaFunctor Q hAS l r ⋙
      A.rightFiniteWindowNakayamaInverseFunctor Q hAS l r).obj M)
    ((A.rightFiniteDimensionalNakayamaEquivalence Q hAS).unitIso.app M.obj)) (by
      intro M N f
      apply ObjectProperty.hom_ext
      exact (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).unitIso.hom.naturality
        ((A.rightFiniteWindowProperty l r).ι.map f))

noncomputable def rightFiniteWindowNakayamaCounitIso (hAS : A.ASRegular Q) (l r : ℤ) :
    A.rightFiniteWindowNakayamaInverseFunctor Q hAS l r ⋙ A.rightFiniteWindowNakayamaFunctor Q hAS l r ≅
      𝟭 (A.RightFiniteWindow (l-Q.vertices) (r-Q.vertices)) :=
  NatIso.ofComponents (fun M => (A.rightFiniteWindowProperty (l-Q.vertices) (r-Q.vertices)).isoMk
    (X := (A.rightFiniteWindowNakayamaInverseFunctor Q hAS l r ⋙
      A.rightFiniteWindowNakayamaFunctor Q hAS l r).obj M) (Y := M)
    ((A.rightFiniteDimensionalNakayamaEquivalence Q hAS).counitIso.app M.obj)) (by
      intro M N f
      apply ObjectProperty.hom_ext
      exact (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).counitIso.hom.naturality
        ((A.rightFiniteWindowProperty (l-Q.vertices) (r-Q.vertices)).ι.map f))

noncomputable def rightFiniteWindowNakayamaEquivalence (hAS : A.ASRegular Q) (l r : ℤ) :
    A.RightFiniteWindow l r ≌ A.RightFiniteWindow (l-Q.vertices) (r-Q.vertices) :=
  CategoryTheory.Equivalence.mk (A.rightFiniteWindowNakayamaFunctor Q hAS l r)
    (A.rightFiniteWindowNakayamaInverseFunctor Q hAS l r)
    (A.rightFiniteWindowNakayamaUnitIso Q hAS l r) (A.rightFiniteWindowNakayamaCounitIso Q hAS l r)

instance rightFiniteWindowNakayamaFunctorAdditive (hAS : A.ASRegular Q) (l r : ℤ) :
    (A.rightFiniteWindowNakayamaFunctor Q hAS l r).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    exact (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor.map_add
      (f := (A.rightFiniteWindowProperty l r).ι.map f) (g := (A.rightFiniteWindowProperty l r).ι.map g)
instance rightFiniteWindowNakayamaFunctorLinear (hAS : A.ASRegular Q) (l r : ℤ) :
    (A.rightFiniteWindowNakayamaFunctor Q hAS l r).Linear k where
  map_smul := by
    intro M N f t
    apply ObjectProperty.hom_ext
    exact (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor.map_smul t
      ((A.rightFiniteWindowProperty l r).ι.map f)

instance rightFiniteWindowNakayamaEquivalenceFunctorAdditive (hAS : A.ASRegular Q) (l r : ℤ) :
    (A.rightFiniteWindowNakayamaEquivalence Q hAS l r).functor.Additive := by
  change (A.rightFiniteWindowNakayamaFunctor Q hAS l r).Additive
  infer_instance
instance rightFiniteWindowNakayamaEquivalenceFunctorLinear (hAS : A.ASRegular Q) (l r : ℤ) :
    (A.rightFiniteWindowNakayamaEquivalence Q hAS l r).functor.Linear k := by
  change (A.rightFiniteWindowNakayamaFunctor Q hAS l r).Linear k
  infer_instance

theorem rightFiniteWindowNakayama_shortExact (hAS : A.ASRegular Q) (l r : ℤ)
    {S : ShortComplex (A.RightFiniteWindow l r)} (hS : S.ShortExact) :
    (S.map (A.rightFiniteWindowNakayamaEquivalence Q hAS l r).functor).ShortExact :=
  hS.map_of_exact _
end ASGinzburg.ZAlgebra
