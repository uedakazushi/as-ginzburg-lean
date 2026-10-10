import work.ASGinzburgDraft.ASCutEnvelopingFiniteResolution
import work.ASGinzburgDraft.FiniteFourTermRingHomComplex

/-! The actual regular enveloping module of an AS cut algebra has its
ring Hom computed by a bounded finite-projective complex of right
enveloping modules. The cohomology objects are the actual right-derived
ring dual, with their actual opposite-enveloping-ring module structure. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v w
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutEnvelopingRingHomCochainComplex (hAS : A.ASRegular Q) :
    CochainComplex (ModuleCat.{v}
      (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))ᵐᵒᵖ) ℤ :=
  (hAS.cutEnvelopingFiniteFourTermResolution A Q).ringHomCochainComplex

theorem ASRegular.cutEnvelopingRingHomCochainComplex_term_finiteProjective
    (hAS : A.ASRegular Q) (i : ℤ) :
    ordinaryFiniteProjectiveProperty
      (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))ᵐᵒᵖ
      ((hAS.cutEnvelopingRingHomCochainComplex A Q).X i) :=
  (hAS.cutEnvelopingFiniteFourTermResolution A Q).ringHomCochainComplex_term_finiteProjective i

theorem ASRegular.cutEnvelopingRingHomCochainComplex_term_finite
    (hAS : A.ASRegular Q) (i : ℤ) :
    Module.Finite (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))ᵐᵒᵖ
      ((hAS.cutEnvelopingRingHomCochainComplex A Q).X i) :=
  ((ordinaryFiniteProjectiveProperty_iff _ _).mp
    (hAS.cutEnvelopingRingHomCochainComplex_term_finiteProjective A Q i)).1

theorem ASRegular.cutEnvelopingRingHomCochainComplex_term_projective
    (hAS : A.ASRegular Q) (i : ℤ) :
    Projective ((hAS.cutEnvelopingRingHomCochainComplex A Q).X i) :=
  ((ordinaryFiniteProjectiveProperty_iff _ _).mp
    (hAS.cutEnvelopingRingHomCochainComplex_term_finiteProjective A Q i)).2

theorem ASRegular.cutEnvelopingRingHomCochainComplex_isZero_outside
    (hAS : A.ASRegular Q) (i : ℤ) (hi : i < 0 ∨ 3 < i) :
    IsZero ((hAS.cutEnvelopingRingHomCochainComplex A Q).X i) :=
  (hAS.cutEnvelopingFiniteFourTermResolution A Q).ringHomCochainComplex_isZero_outside i hi

theorem ASRegular.cutEnvelopingRingHomCochainComplex_perfect (hAS : A.ASRegular Q) :
    ordinaryFiniteProjectiveCochainProperty
      (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))ᵐᵒᵖ
      (hAS.cutEnvelopingRingHomCochainComplex A Q) :=
  (hAS.cutEnvelopingFiniteFourTermResolution A Q).ringHomCochainComplex_perfect

noncomputable def ASRegular.cutEnvelopingRingDualExtObject (hAS : A.ASRegular Q) (n : ℕ) :
    ModuleCat.{v} (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))ᵐᵒᵖ :=
  (ordinaryRingDualExtFunctor (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q)) n).obj
    (op (regularEnvelopingModuleCat k (hAS.CutGradedAlgebra A Q)))

noncomputable def ASRegular.cutEnvelopingRingDualExtCochainHomologyIso
    (hAS : A.ASRegular Q) (n : ℕ) :
    hAS.cutEnvelopingRingDualExtObject A Q n ≅
      (hAS.cutEnvelopingRingHomCochainComplex A Q).homology (n : ℤ) :=
  (hAS.cutEnvelopingFiniteFourTermResolution A Q).ringDualExtCochainHomologyIso n

theorem ASRegular.cutEnvelopingRingDualExt_isZero_ge_four
    (hAS : A.ASRegular Q) (n : ℕ) :
    IsZero (hAS.cutEnvelopingRingDualExtObject A Q (n + 4)) :=
  (hAS.cutEnvelopingFiniteFourTermResolution A Q).ringDualExt_isZero_ge_four n

theorem ASRegular.cutEnvelopingRingDualExt_three_finite (hAS : A.ASRegular Q) :
    Module.Finite (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))ᵐᵒᵖ
      (hAS.cutEnvelopingRingDualExtObject A Q 3) :=
  (hAS.cutEnvelopingFiniteFourTermResolution A Q).ringDualExt_three_finite

theorem ASRegular.cutEnvelopingRingHomPerfectDerived (hAS : A.ASRegular Q)
    [HasDerivedCategory.{w}
      (ModuleCat.{v} (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))ᵐᵒᵖ)] :
    ordinaryPerfectDerivedProperty (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))ᵐᵒᵖ
      (DerivedCategory.Q.obj (hAS.cutEnvelopingRingHomCochainComplex A Q)) :=
  (hAS.cutEnvelopingFiniteFourTermResolution A Q).ringHomPerfectDerived

end ASGinzburg.ZAlgebra
