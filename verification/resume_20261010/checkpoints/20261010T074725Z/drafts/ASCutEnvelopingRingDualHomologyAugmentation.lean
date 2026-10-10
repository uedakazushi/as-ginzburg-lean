import work.ASGinzburgDraft.ASCutEnvelopingRingDualExtConcentration
import ASGinzburg.HomologyAugmentation

/-! The actual native enveloping ring-dual complex admits its canonical
quasi-isomorphism to its genuine degree-three homology, from original AS. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutEnvelopingMinimalRingHom_homology_isZero_other
    (hAS : A.ASRegular Q) (n : ℕ) (hn : n ≠ 3) :
    IsZero ((hAS.cutEnvelopingMinimalRingHomNatComplex A Q).homology n) :=
  IsZero.of_iso (hAS.cutEnvelopingRingDualExt_isZero_other A Q n hn)
    (hAS.cutEnvelopingMinimalRingDualExtHomologyIso A Q n).symm

theorem ASRegular.cutEnvelopingMinimalRingHom_top_outgoing_zero
    (hAS : A.ASRegular Q) :
    ((hAS.cutEnvelopingMinimalRingHomNatComplex A Q).sc 3).g = 0 := by
  let K := hAS.cutEnvelopingMinimalRingHomNatComplex A Q
  change K.d 3 ((ComplexShape.up ℕ).next 3) = 0
  rw [CochainComplex.next]
  exact (hAS.cutEnvelopingMinimalRingHomNatComplex_isZero_ge_four A Q 0).eq_of_tgt _ _

noncomputable def ASRegular.cutEnvelopingMinimalRingHomTopAugmentation
    (hAS : A.ASRegular Q) :
    hAS.cutEnvelopingMinimalRingHomNatComplex A Q ⟶
      (HomologicalComplex.single (ModuleCat.{v}
        (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))ᵐᵒᵖ)
        (ComplexShape.up ℕ) 3).obj
          ((hAS.cutEnvelopingMinimalRingHomNatComplex A Q).homology 3) :=
  homologyAugmentation (hAS.cutEnvelopingMinimalRingHomNatComplex A Q) 3
    (hAS.cutEnvelopingMinimalRingHom_top_outgoing_zero A Q)

theorem ASRegular.cutEnvelopingMinimalRingHomTopAugmentation_quasiIso
    (hAS : A.ASRegular Q) :
    QuasiIso (hAS.cutEnvelopingMinimalRingHomTopAugmentation A Q) :=
  (homologyAugmentation_quasiIso_iff _ 3
    (hAS.cutEnvelopingMinimalRingHom_top_outgoing_zero A Q)).mpr
      (hAS.cutEnvelopingMinimalRingHom_homology_isZero_other A Q)

end ASGinzburg.ZAlgebra
