import ASGinzburg.NakayamaRepresentableUnderlying


/-! Choose the proved simple isomorphism once per vertex and normalize all finite-window projective-cover isomorphisms with the same choice. -/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

/-- Choose once for each vertex from the already proved simple isomorphism.
This packages an actual existence proof, rather than adding an assumption. -/
noncomputable def rightFiniteDimensionalNakayamaSimpleChosenIso (hAS : A.ASRegular Q) (i : ℤ) :
    (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor.obj
      (A.rightFiniteDimensionalSimple i) ≅ A.rightFiniteDimensionalSimple (i-Q.vertices) :=
  Classical.choice ⟨A.rightFiniteDimensionalNakayamaSimpleHeightIso Q hAS i⟩

noncomputable def rightFiniteWindowNakayamaChosenSimpleIso (hAS : A.ASRegular Q)
    (l r i : ℤ) (hli : l ≤ i) (hir : i ≤ r) :
    (A.rightFiniteWindowNakayamaEquivalence Q hAS l r).functor.obj
      (A.rightFiniteWindowSimple l r i hli hir) ≅
      A.rightFiniteWindowSimple (l-Q.vertices) (r-Q.vertices) (i-Q.vertices)
        (sub_le_sub_right hli _) (sub_le_sub_right hir _) :=
  A.rightFiniteWindowNakayamaSimpleIsoWith Q hAS l r i hli hir
    (A.rightFiniteDimensionalNakayamaSimpleChosenIso Q hAS i)

theorem rightFiniteWindowNakayamaChosenSimpleIso_hom_eq (hAS : A.ASRegular Q)
    (l r i : ℤ) (hli : l ≤ i) (hir : i ≤ r) :
    (A.rightFiniteWindowNakayamaChosenSimpleIso Q hAS l r i hli hir).hom =
      (A.rightFiniteDimensionalNakayamaSimpleChosenIso Q hAS i).hom := rfl

noncomputable def rightFiniteWindowNakayamaChosenRepresentableCover (hAS : A.ASRegular Q)
    (l r i : ℤ) (hli : l ≤ i) (hir : i ≤ r) :
    (A.rightFiniteWindowNakayamaEquivalence Q hAS l r).functor.obj
      (A.rightFiniteWindowRepresentable l r i hir) ⟶
      A.rightFiniteWindowSimple (l-Q.vertices) (r-Q.vertices) (i-Q.vertices)
        (sub_le_sub_right hli _) (sub_le_sub_right hir _) :=
  (A.rightFiniteWindowNakayamaEquivalence Q hAS l r).functor.map
    (A.rightFiniteWindowRepresentableCover l r i hli hir) ≫
      (A.rightFiniteWindowNakayamaChosenSimpleIso Q hAS l r i hli hir).hom

instance rightFiniteWindowNakayamaChosenRepresentableCoverEpi (hAS : A.ASRegular Q)
    (l r i : ℤ) (hli : l ≤ i) (hir : i ≤ r) :
    Epi (A.rightFiniteWindowNakayamaChosenRepresentableCover Q hAS l r i hli hir) := by
  dsimp [rightFiniteWindowNakayamaChosenRepresentableCover]
  infer_instance

theorem rightFiniteWindowNakayamaChosenRepresentableCover_nonzero (hAS : A.ASRegular Q)
    (l r i : ℤ) (hli : l ≤ i) (hir : i ≤ r) :
    A.rightFiniteWindowNakayamaChosenRepresentableCover Q hAS l r i hli hir ≠ 0 := by
  intro h
  have H := IsZero.of_epi_eq_zero _ h
  have H' := A.rightFiniteDimensionalProperty.ι.map_isZero
    ((A.rightFiniteWindowProperty (l-Q.vertices) (r-Q.vertices)).ι.map_isZero H)
  exact Simple.not_isZero (A.simpleRightModule (i-Q.vertices)) H'

theorem rightFiniteWindowNakayamaChosenRepresentable_cover_rigidity (hAS : A.ASRegular Q)
    (l r i : ℤ) (hli : l ≤ i) (hir : i ≤ r)
    (t : (A.rightFiniteWindowNakayamaEquivalence Q hAS l r).functor.obj
      (A.rightFiniteWindowRepresentable l r i hir) ⟶
      (A.rightFiniteWindowNakayamaEquivalence Q hAS l r).functor.obj
        (A.rightFiniteWindowRepresentable l r i hir))
    (ht : t ≫ A.rightFiniteWindowNakayamaChosenRepresentableCover Q hAS l r i hli hir =
      A.rightFiniteWindowNakayamaChosenRepresentableCover Q hAS l r i hli hir) : t = 𝟙 _ :=
  ASGinzburg.endomorphism_eq_id_of_preserves_nonzero_map
    (A.rightFiniteWindowNakayamaRepresentableEnd_finrank Q hAS l r i hli hir) _
    (A.rightFiniteWindowNakayamaChosenRepresentableCover_nonzero Q hAS l r i hli hir) t ht

noncomputable def rightFiniteWindowNakayamaChosenRepresentableIso (hAS : A.ASRegular Q)
    (l r i : ℤ) (hli : l ≤ i) (hir : i ≤ r) :
    (A.rightFiniteWindowNakayamaEquivalence Q hAS l r).functor.obj
      (A.rightFiniteWindowRepresentable l r i hir) ≅
      A.rightFiniteWindowRepresentable (l-Q.vertices) (r-Q.vertices) (i-Q.vertices)
        (sub_le_sub_right hir _) :=
  ASGinzburg.normalizedProjectiveIso
    (A.rightFiniteWindowNakayamaChosenRepresentableCover Q hAS l r i hli hir)
    (A.rightFiniteWindowRepresentableCover (l-Q.vertices) (r-Q.vertices) (i-Q.vertices)
      (sub_le_sub_right hli _) (sub_le_sub_right hir _))
    (A.rightFiniteWindowNakayamaChosenRepresentable_cover_rigidity Q hAS l r i hli hir)
    (A.rightFiniteWindowRepresentable_cover_rigidity (l-Q.vertices) (r-Q.vertices) (i-Q.vertices)
      (sub_le_sub_right hli _) (sub_le_sub_right hir _))

theorem rightFiniteWindowNakayamaChosenRepresentableIso_hom_cover (hAS : A.ASRegular Q)
    (l r i : ℤ) (hli : l ≤ i) (hir : i ≤ r) :
    (A.rightFiniteWindowNakayamaChosenRepresentableIso Q hAS l r i hli hir).hom ≫
      A.rightFiniteWindowRepresentableCover (l-Q.vertices) (r-Q.vertices) (i-Q.vertices)
        (sub_le_sub_right hli _) (sub_le_sub_right hir _) =
      A.rightFiniteWindowNakayamaChosenRepresentableCover Q hAS l r i hli hir :=
  ASGinzburg.normalizedProjectiveIso_hom_comp _ _ _ _

noncomputable def rightFiniteWindowNakayamaChosenRepresentableModuleIso (hAS : A.ASRegular Q)
    (l r i : ℤ) (hli : l ≤ i) (hir : i ≤ r) :
    A.rightFiniteDimensionalNakayamaUnderlying Q hAS (A.rightTruncatedRepresentable l i)
        (A.rightTruncatedRepresentable_finite l i) ≅
      A.rightTruncatedRepresentable (l-Q.vertices) (i-Q.vertices) :=
  { hom := (A.rightFiniteWindowNakayamaChosenRepresentableIso Q hAS l r i hli hir).hom
    inv := (A.rightFiniteWindowNakayamaChosenRepresentableIso Q hAS l r i hli hir).inv
    hom_inv_id := (A.rightFiniteWindowNakayamaChosenRepresentableIso Q hAS l r i hli hir).hom_inv_id
    inv_hom_id := (A.rightFiniteWindowNakayamaChosenRepresentableIso Q hAS l r i hli hir).inv_hom_id }

theorem rightFiniteWindowNakayamaChosenRepresentableModuleIso_hom_cover (hAS : A.ASRegular Q)
    (l r i : ℤ) (hli : l ≤ i) (hir : i ≤ r) :
    (A.rightFiniteWindowNakayamaChosenRepresentableModuleIso Q hAS l r i hli hir).hom ≫
        A.rightTruncatedRepresentableSimpleCover (l-Q.vertices) (i-Q.vertices) (sub_le_sub_right hli _) =
      A.rightFiniteDimensionalNakayamaUnderlyingMap Q hAS
        (A.rightTruncatedRepresentable_finite l i) (A.rightFiniteDimensional_simple i)
        (A.rightTruncatedRepresentableSimpleCover l i hli) ≫
          (A.rightFiniteDimensionalNakayamaSimpleChosenIso Q hAS i).hom :=
  A.rightFiniteWindowNakayamaChosenRepresentableIso_hom_cover Q hAS l r i hli hir

end ASGinzburg.ZAlgebra
