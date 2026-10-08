import ASGinzburg.NakayamaWindowNormalization
import ASGinzburg.Conjugation
import ASGinzburg.WindowPeriodicity

/-! Recover multiplicative algebra-component maps from the normalized finite-window Nakayama equivalence. -/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
@[reassoc] theorem rightFiniteWindowNakayamaChosenRepresentableModuleIso_restriction (hAS : A.ASRegular Q)
    (l r l' r' i : ℤ) (hli : l ≤ i) (hir : i ≤ r) (hl : l' ≤ l) (hr : r ≤ r') :
    A.rightFiniteDimensionalNakayamaUnderlyingMap Q hAS
        (A.rightTruncatedRepresentable_finite l' i) (A.rightTruncatedRepresentable_finite l i)
        (A.rightTruncatedRepresentableRestriction l' l i hl) ≫
          (A.rightFiniteWindowNakayamaChosenRepresentableModuleIso Q hAS l r i hli hir).hom =
      (A.rightFiniteWindowNakayamaChosenRepresentableModuleIso Q hAS l' r' i (hl.trans hli) (hir.trans hr)).hom ≫
        A.rightTruncatedRepresentableRestriction (l'-Q.vertices) (l-Q.vertices) (i-Q.vertices)
          (sub_le_sub_right hl _) := by
  let e := A.rightFiniteWindowNakayamaChosenRepresentableModuleIso Q hAS l r i hli hir
  let e' := A.rightFiniteWindowNakayamaChosenRepresentableModuleIso Q hAS l' r' i (hl.trans hli) (hir.trans hr)
  let q := A.rightFiniteDimensionalNakayamaUnderlyingMap Q hAS
    (A.rightTruncatedRepresentable_finite l' i) (A.rightTruncatedRepresentable_finite l i)
    (A.rightTruncatedRepresentableRestriction l' l i hl)
  let q' := A.rightTruncatedRepresentableRestriction (l'-Q.vertices) (l-Q.vertices) (i-Q.vertices)
    (sub_le_sub_right hl _)
  let p := A.rightTruncatedRepresentableSimpleCover (l-Q.vertices) (i-Q.vertices) (sub_le_sub_right hli _)
  let p' := A.rightTruncatedRepresentableSimpleCover (l'-Q.vertices) (i-Q.vertices)
    (sub_le_sub_right (hl.trans hli) _)
  let γ := (A.rightFiniteDimensionalNakayamaSimpleChosenIso Q hAS i).hom
  let np := A.rightFiniteDimensionalNakayamaUnderlyingMap Q hAS
    (A.rightTruncatedRepresentable_finite l i) (A.rightFiniteDimensional_simple i)
    (A.rightTruncatedRepresentableSimpleCover l i hli)
  let np' := A.rightFiniteDimensionalNakayamaUnderlyingMap Q hAS
    (A.rightTruncatedRepresentable_finite l' i) (A.rightFiniteDimensional_simple i)
    (A.rightTruncatedRepresentableSimpleCover l' i (hl.trans hli))
  have he : e.hom ≫ p = np ≫ γ := A.rightFiniteWindowNakayamaChosenRepresentableModuleIso_hom_cover Q hAS l r i hli hir
  have he' : e'.hom ≫ p' = np' ≫ γ := A.rightFiniteWindowNakayamaChosenRepresentableModuleIso_hom_cover Q hAS l' r' i _ _
  have hq : q ≫ np = np' := by
    dsimp [q,np,np']
    rw [← A.rightFiniteDimensionalNakayamaUnderlyingMap_comp,
      A.rightTruncatedRepresentableRestriction_cover]
  have hq' : q' ≫ p = p' := A.rightTruncatedRepresentableRestriction_cover _ _ _ _ _
  letI : IsIso ((A.rightModuleEvaluation (i-Q.vertices)).map p) :=
    A.rightTruncatedRepresentableSimpleCover_component_isIso _ _ _
  have h : e'.inv ≫ q ≫ e.hom = q' := by
    apply A.rightTruncatedRepresentable_postcomp_injective (l'-Q.vertices) (i-Q.vertices)
      (fun j hj => A.rightTruncatedRepresentable_below (l-Q.vertices) (i-Q.vertices) j (by omega))
      (fun j hj => A.simpleRightModule_off_diagonal (i-Q.vertices) j (by omega)) p
    calc
      (e'.inv ≫ q ≫ e.hom) ≫ p = e'.inv ≫ q ≫ (np ≫ γ) := by simp only [Category.assoc,he]
      _ = e'.inv ≫ np' ≫ γ := by rw [← Category.assoc q np γ,hq]
      _ = e'.inv ≫ e'.hom ≫ p' := by rw [← he']
      _ = p' := by simp
      _ = q' ≫ p := hq'.symm
  change q ≫ e.hom = e'.hom ≫ q'
  rw [← h]
  simp

noncomputable def rightFiniteWindowNakayamaComponentEquiv (hAS : A.ASRegular Q)
    (l r i j : ℤ) (hi : InWindow l r i) (hj : InWindow l r j) :
    A.Hom i j ≃ₗ[k] A.Hom (i-Q.vertices) (j-Q.vertices) := by
  let E := (A.rightFiniteWindowNakayamaEquivalence Q hAS l r).functor
  let P := A.rightFiniteWindowRepresentable l r i hi.2
  let R := A.rightFiniteWindowRepresentable l r j hj.2
  let h : (P ⟶ R) ≃ₗ[k] (E.obj P ⟶ E.obj R) :=
    LinearEquiv.ofBijective (E.mapLinearMap k) ⟨E.map_injective,E.map_surjective⟩
  exact (A.rightTruncatedRepresentableHomComponentEquiv l i j hi.1).trans
    ((h.trans (Linear.homCongr k
      (A.rightFiniteWindowNakayamaChosenRepresentableIso Q hAS l r i hi.1 hi.2)
      (A.rightFiniteWindowNakayamaChosenRepresentableIso Q hAS l r j hj.1 hj.2))).trans
        (A.rightTruncatedRepresentableHomComponentEquiv (l-Q.vertices) (i-Q.vertices) (j-Q.vertices)
          (sub_le_sub_right hi.1 _)).symm)

theorem rightFiniteWindowNakayamaComponentEquiv_hom (hAS : A.ASRegular Q)
    (l r i j : ℤ) (hi : InWindow l r i) (hj : InWindow l r j) (x : A.Hom i j) :
    A.rightTruncatedRepresentableHomComponentEquiv (l-Q.vertices) (i-Q.vertices) (j-Q.vertices)
        (sub_le_sub_right hi.1 _) (A.rightFiniteWindowNakayamaComponentEquiv Q hAS l r i j hi hj x) =
      (A.rightFiniteWindowNakayamaChosenRepresentableModuleIso Q hAS l r i hi.1 hi.2).inv ≫
        A.rightFiniteDimensionalNakayamaUnderlyingMap Q hAS (A.rightTruncatedRepresentable_finite l i)
          (A.rightTruncatedRepresentable_finite l j) (A.rightTruncatedRepresentableHomComponentEquiv l i j hi.1 x) ≫
            (A.rightFiniteWindowNakayamaChosenRepresentableModuleIso Q hAS l r j hj.1 hj.2).hom := by
  unfold rightFiniteWindowNakayamaComponentEquiv
  rw [LinearEquiv.trans_apply,LinearEquiv.trans_apply,LinearEquiv.trans_apply]
  change (A.rightTruncatedRepresentableHomComponentEquiv (l-Q.vertices) (i-Q.vertices) (j-Q.vertices)
    (sub_le_sub_right hi.1 _))
      ((A.rightTruncatedRepresentableHomComponentEquiv (l-Q.vertices) (i-Q.vertices) (j-Q.vertices)
        (sub_le_sub_right hi.1 _)).symm _) = _
  refine ((A.rightTruncatedRepresentableHomComponentEquiv (l-Q.vertices) (i-Q.vertices) (j-Q.vertices)
    (sub_le_sub_right hi.1 _)).apply_symm_apply _).trans ?_
  change _ ≫ A.rightFiniteDimensionalProperty.ι.map
    ((A.rightFiniteWindowProperty (l-Q.vertices) (r-Q.vertices)).ι.map
      ((A.rightFiniteWindowNakayamaEquivalence Q hAS l r).functor.map
        (show A.rightFiniteWindowRepresentable l r i hi.2 ⟶ A.rightFiniteWindowRepresentable l r j hj.2 from
          A.rightTruncatedRepresentableHomComponentEquiv l i j hi.1 x))) ≫ _ = _
  rw [A.rightFiniteWindowNakayamaFunctor_underlying_map]
  rfl

theorem rightFiniteWindowNakayamaComponentEquiv_id (hAS : A.ASRegular Q)
    (l r i : ℤ) (hi : InWindow l r i) :
    A.rightFiniteWindowNakayamaComponentEquiv Q hAS l r i i hi hi (A.id i) = A.id (i-Q.vertices) := by
  apply (A.rightTruncatedRepresentableHomComponentEquiv (l-Q.vertices) (i-Q.vertices) (i-Q.vertices)
    (sub_le_sub_right hi.1 _)).injective
  rw [A.rightFiniteWindowNakayamaComponentEquiv_hom,A.rightTruncatedRepresentableHomComponentEquiv_id,
    A.rightTruncatedRepresentableHomComponentEquiv_id]
  change _ ≫ (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor.map
    (𝟙 (⟨A.rightTruncatedRepresentable l i,A.rightTruncatedRepresentable_finite l i⟩ : A.RightFiniteDimensional)) ≫ _ = _
  rw [CategoryTheory.Functor.map_id]
  exact (A.rightFiniteWindowNakayamaChosenRepresentableModuleIso Q hAS l r i hi.1 hi.2).inv_hom_id

theorem rightFiniteWindowNakayamaComponentEquiv_comp (hAS : A.ASRegular Q)
    (l r i j m : ℤ) (hi : InWindow l r i) (hj : InWindow l r j) (hm : InWindow l r m)
    (f : A.Hom i j) (g : A.Hom j m) :
    A.rightFiniteWindowNakayamaComponentEquiv Q hAS l r i m hi hm (A.comp g f) =
      A.comp (A.rightFiniteWindowNakayamaComponentEquiv Q hAS l r j m hj hm g)
        (A.rightFiniteWindowNakayamaComponentEquiv Q hAS l r i j hi hj f) := by
  apply (A.rightTruncatedRepresentableHomComponentEquiv (l-Q.vertices) (i-Q.vertices) (m-Q.vertices)
    (sub_le_sub_right hi.1 _)).injective
  rw [A.rightTruncatedRepresentableHomComponentEquiv_comp _ _ _ _ _ (sub_le_sub_right hj.1 _),
    A.rightFiniteWindowNakayamaComponentEquiv_hom,A.rightFiniteWindowNakayamaComponentEquiv_hom,
    A.rightFiniteWindowNakayamaComponentEquiv_hom,
    A.rightTruncatedRepresentableHomComponentEquiv_comp l i j m hi.1 hj.1,
    A.rightFiniteDimensionalNakayamaUnderlyingMap_comp Q hAS _ (A.rightTruncatedRepresentable_finite l j)]
  simp [Category.assoc]
end ASGinzburg.ZAlgebra
