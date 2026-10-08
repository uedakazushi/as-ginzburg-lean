import ASGinzburg.NakayamaWindowComponents


/-! Compatibility of the actual algebra-component translations on enlarging finite windows. -/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem rightFiniteWindowNakayamaComponentEquiv_coherent (hAS : A.ASRegular Q)
    (l r l' r' i j : ℤ) (hi : InWindow l r i) (hj : InWindow l r j)
    (hl : l' ≤ l) (hr : r ≤ r') :
    A.rightFiniteWindowNakayamaComponentEquiv Q hAS l r i j hi hj =
      A.rightFiniteWindowNakayamaComponentEquiv Q hAS l' r' i j (hi.mono hl hr) (hj.mono hl hr) := by
  apply LinearEquiv.ext
  intro x
  let eI := A.rightFiniteWindowNakayamaChosenRepresentableModuleIso Q hAS l r i hi.1 hi.2
  let eJ := A.rightFiniteWindowNakayamaChosenRepresentableModuleIso Q hAS l r j hj.1 hj.2
  let eI' := A.rightFiniteWindowNakayamaChosenRepresentableModuleIso Q hAS l' r' i
    (hl.trans hi.1) (hi.2.trans hr)
  let eJ' := A.rightFiniteWindowNakayamaChosenRepresentableModuleIso Q hAS l' r' j
    (hl.trans hj.1) (hj.2.trans hr)
  let qi := A.rightTruncatedRepresentableRestriction l' l i hl
  let qj := A.rightTruncatedRepresentableRestriction l' l j hl
  let qi' := A.rightTruncatedRepresentableRestriction (l'-Q.vertices) (l-Q.vertices) (i-Q.vertices)
    (sub_le_sub_right hl _)
  let qj' := A.rightTruncatedRepresentableRestriction (l'-Q.vertices) (l-Q.vertices) (j-Q.vertices)
    (sub_le_sub_right hl _)
  let ni := A.rightFiniteDimensionalNakayamaUnderlyingMap Q hAS
    (A.rightTruncatedRepresentable_finite l' i) (A.rightTruncatedRepresentable_finite l i) qi
  let nj := A.rightFiniteDimensionalNakayamaUnderlyingMap Q hAS
    (A.rightTruncatedRepresentable_finite l' j) (A.rightTruncatedRepresentable_finite l j) qj
  let f := A.rightTruncatedRepresentableHomComponentEquiv l i j hi.1 x
  let f' := A.rightTruncatedRepresentableHomComponentEquiv l' i j (hl.trans hi.1) x
  let nf := A.rightFiniteDimensionalNakayamaUnderlyingMap Q hAS
    (A.rightTruncatedRepresentable_finite l i) (A.rightTruncatedRepresentable_finite l j) f
  let nf' := A.rightFiniteDimensionalNakayamaUnderlyingMap Q hAS
    (A.rightTruncatedRepresentable_finite l' i) (A.rightTruncatedRepresentable_finite l' j) f'
  have hI : ni ≫ eI.hom = eI'.hom ≫ qi' :=
    A.rightFiniteWindowNakayamaChosenRepresentableModuleIso_restriction Q hAS l r l' r' i hi.1 hi.2 hl hr
  have hJ : nj ≫ eJ.hom = eJ'.hom ≫ qj' :=
    A.rightFiniteWindowNakayamaChosenRepresentableModuleIso_restriction Q hAS l r l' r' j hj.1 hj.2 hl hr
  have hIinv : qi' ≫ eI.inv = eI'.inv ≫ ni := by
    apply (cancel_mono eI.hom).mp
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
    rw [hI]
    simp
  have hnat : ni ≫ nf = nf' ≫ nj := by
    dsimp [ni,nf,nf',nj,f,f',qi,qj]
    rw [← A.rightFiniteDimensionalNakayamaUnderlyingMap_comp,
      ← A.rightFiniteDimensionalNakayamaUnderlyingMap_comp,
      A.rightTruncatedRepresentableRestriction_hom]
  apply (A.rightTruncatedRepresentableHomComponentEquiv (l-Q.vertices) (i-Q.vertices) (j-Q.vertices)
    (sub_le_sub_right hi.1 _)).injective
  letI : Epi qi' := by dsimp [qi']; infer_instance
  apply (cancel_epi qi').mp
  rw [A.rightFiniteWindowNakayamaComponentEquiv_hom]
  change qi' ≫ eI.inv ≫ nf ≫ eJ.hom = _
  rw [← Category.assoc qi' eI.inv, hIinv, Category.assoc,
    ← Category.assoc ni nf,hnat,Category.assoc nf' nj,hJ]
  rw [← Category.assoc nf' eJ'.hom qj',
    ← Category.assoc eI'.inv (nf' ≫ eJ'.hom) qj']
  rw [← A.rightFiniteWindowNakayamaComponentEquiv_hom Q hAS l' r' i j (hi.mono hl hr) (hj.mono hl hr)]
  exact (A.rightTruncatedRepresentableRestriction_hom (l'-Q.vertices) (l-Q.vertices)
    (i-Q.vertices) (j-Q.vertices) (sub_le_sub_right hl _) (sub_le_sub_right hi.1 _) _)

end ASGinzburg.ZAlgebra
