import work.ASGinzburgDraft.ASCutEnvelopingRingDualExtConcentration
import ASGinzburg.HomologyAugmentation

/-! Original AS regularity concentrates the actual bounded enveloping
ring-dual cochain model in degree three. Its canonical homology
augmentation gives the actual derived-category concentration isomorphism. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v w
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutEnvelopingRingHomCochainHomology_isZero_other
    (hAS : A.ASRegular Q) (i : ℤ) (hi : i ≠ 3) :
    IsZero ((hAS.cutEnvelopingRingHomCochainComplex A Q).homology i) := by
  by_cases hn : i < 0
  · exact ((hAS.cutEnvelopingRingHomCochainComplex A Q).sc i).isZero_homology_of_isZero_X₂
      (hAS.cutEnvelopingRingHomCochainComplex_isZero_outside A Q i (Or.inl hn))
  · have he : i = (i.toNat : ℤ) := Int.eq_natCast_toNat.mpr (le_of_not_gt hn)
    have hne : i.toNat ≠ 3 := by omega
    rw [he]
    exact IsZero.of_iso (hAS.cutEnvelopingRingDualExt_isZero_other A Q i.toNat hne)
      (hAS.cutEnvelopingRingDualExtCochainHomologyIso A Q i.toNat).symm

theorem ASRegular.cutEnvelopingRingHomCochain_top_outgoing_zero
    (hAS : A.ASRegular Q) :
    ((hAS.cutEnvelopingRingHomCochainComplex A Q).sc 3).g = 0 := by
  let K := hAS.cutEnvelopingRingHomCochainComplex A Q
  change K.d 3 ((ComplexShape.up ℤ).next 3) = 0
  have hn : (ComplexShape.up ℤ).next 3 = 4 := by simp
  rw [hn]
  exact (hAS.cutEnvelopingRingHomCochainComplex_isZero_outside A Q 4
    (Or.inr (by omega))).eq_of_tgt _ _

noncomputable def ASRegular.cutEnvelopingRingHomCochainTopAugmentation
    (hAS : A.ASRegular Q) :
    hAS.cutEnvelopingRingHomCochainComplex A Q ⟶
      (HomologicalComplex.single (ModuleCat.{v}
        (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))ᵐᵒᵖ)
        (ComplexShape.up ℤ) 3).obj
          ((hAS.cutEnvelopingRingHomCochainComplex A Q).homology 3) :=
  homologyAugmentation (hAS.cutEnvelopingRingHomCochainComplex A Q) 3
    (hAS.cutEnvelopingRingHomCochain_top_outgoing_zero A Q)

theorem ASRegular.cutEnvelopingRingHomCochainTopAugmentation_quasiIso
    (hAS : A.ASRegular Q) :
    QuasiIso (hAS.cutEnvelopingRingHomCochainTopAugmentation A Q) :=
  (homologyAugmentation_quasiIso_iff _ 3
    (hAS.cutEnvelopingRingHomCochain_top_outgoing_zero A Q)).mpr
      (hAS.cutEnvelopingRingHomCochainHomology_isZero_other A Q)

noncomputable def ASRegular.cutEnvelopingRingHomDerivedConcentrationIso
    (hAS : A.ASRegular Q)
    [HasDerivedCategory.{w}
      (ModuleCat.{v} (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))ᵐᵒᵖ)] :
    DerivedCategory.Q.obj (hAS.cutEnvelopingRingHomCochainComplex A Q) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{v}
        (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))ᵐᵒᵖ) 3).obj
          (hAS.cutEnvelopingRingDualExtObject A Q 3) := by
  let C := ModuleCat.{v} (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))ᵐᵒᵖ
  let K := hAS.cutEnvelopingRingHomCochainComplex A Q
  letI := hAS.cutEnvelopingRingHomCochainTopAugmentation_quasiIso A Q
  exact asIso (DerivedCategory.Q.map (hAS.cutEnvelopingRingHomCochainTopAugmentation A Q)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ C 3).app (K.homology 3)).symm ≪≫
      (DerivedCategory.singleFunctor C 3).mapIso
        (hAS.cutEnvelopingRingDualExtCochainHomologyIso A Q 3).symm

theorem ASRegular.cutEnvelopingRingDualExt_three_derived_perfect
    (hAS : A.ASRegular Q)
    [HasDerivedCategory.{w}
      (ModuleCat.{v} (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))ᵐᵒᵖ)] :
    ordinaryPerfectDerivedProperty (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))ᵐᵒᵖ
      ((DerivedCategory.singleFunctor (ModuleCat.{v}
        (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))ᵐᵒᵖ) 3).obj
          (hAS.cutEnvelopingRingDualExtObject A Q 3)) :=
  ordinaryPerfectDerivedProperty_of_iso _ (hAS.cutEnvelopingRingHomDerivedConcentrationIso A Q).symm
    (hAS.cutEnvelopingRingHomPerfectDerived A Q)

end ASGinzburg.ZAlgebra
