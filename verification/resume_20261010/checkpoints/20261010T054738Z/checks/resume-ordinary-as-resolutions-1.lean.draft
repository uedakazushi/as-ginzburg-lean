import work.ASGinzburgDraft.PeriodCutForgetExactness
import work.ASGinzburgDraft.PeriodCutOrdinaryFiniteProjectives
import ASGinzburg.MapProjectiveResolutionOfTerms
import ASGinzburg.ASCutGradedResolutionFiniteness

/-! Forgetting the internal grading yields a genuine four-term
projective resolution in ordinary right-R ModuleCat. Every term is
finitely generated and projective from the original AS condition. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutOrdinarySimple (hAS : A.ASRegular Q)
    (x : Q.LiftVertex) : ModuleCat.{v} (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ :=
  (hAS.cutGradedSimple A Q x).ringModule

theorem ASRegular.cutCornerResolution_ring_projective (hAS : A.ASRegular Q)
    (x : Q.LiftVertex) (n : ℕ) :
    Projective (((hAS.periodIso A Q).cornerModuleRingFunctor Q).obj
      (((hAS.cutCornerASRegular Q).projectiveResolution (hAS.cutCornerCover A Q) Q x).complex.X n)) := by
  change Projective (((hAS.periodIso A Q).cornerModuleRingFunctor Q).obj
    (((hAS.cutCornerASRegular Q).resolution (hAS.cutCornerCover A Q) Q x).complexTerm n))
  exact (hAS.periodIso A Q).cornerFiniteProjective_ring_projective Q
    (((hAS.cutCornerASRegular Q).resolution (hAS.cutCornerCover A Q) Q x).complexTermFiniteProjective n)

noncomputable def ASRegular.cutOrdinarySimpleProjectiveResolution (hAS : A.ASRegular Q)
    (x : Q.LiftVertex) : ProjectiveResolution (hAS.cutOrdinarySimple A Q x) :=
  mapProjectiveResolutionOfTerms ((hAS.periodIso A Q).cornerModuleRingFunctor Q)
    ((hAS.cutCornerASRegular Q).projectiveResolution (hAS.cutCornerCover A Q) Q x)
    (hAS.cutCornerResolution_ring_projective A Q x)

theorem ASRegular.cutOrdinarySimpleProjectiveResolution_finite (hAS : A.ASRegular Q)
    (x : Q.LiftVertex) (n : ℕ) :
    Module.Finite (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ
      ((hAS.cutOrdinarySimpleProjectiveResolution A Q x).complex.X n) := by
  change Module.Finite (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ
    (((hAS.periodIso A Q).cornerModuleRingFunctor Q).obj
      (((hAS.cutCornerASRegular Q).resolution (hAS.cutCornerCover A Q) Q x).complexTerm n))
  exact (hAS.periodIso A Q).cornerFiniteProjective_ring_finite Q
    (((hAS.cutCornerASRegular Q).resolution (hAS.cutCornerCover A Q) Q x).complexTermFiniteProjective n)

theorem ASRegular.cutOrdinarySimpleProjectiveResolution_isZero_ge_four
    (hAS : A.ASRegular Q) (x : Q.LiftVertex) (n : ℕ) :
    IsZero ((hAS.cutOrdinarySimpleProjectiveResolution A Q x).complex.X (n+4)) :=
  mapProjectiveResolutionOfTerms_isZero ((hAS.periodIso A Q).cornerModuleRingFunctor Q)
    ((hAS.cutCornerASRegular Q).projectiveResolution (hAS.cutCornerCover A Q) Q x)
    (hAS.cutCornerResolution_ring_projective A Q x) (n+4)
    ((hAS.cutCornerASRegular Q).projectiveResolution_isZero_ge_four
      (hAS.cutCornerCover A Q) Q x n)

end ASGinzburg.ZAlgebra
