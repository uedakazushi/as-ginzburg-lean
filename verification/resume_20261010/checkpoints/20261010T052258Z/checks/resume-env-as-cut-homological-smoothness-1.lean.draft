import work.ASGinzburgDraft.ASCutEnvelopingFiniteResolution
import work.ASGinzburgDraft.AlgebraHomologicalSmoothness
import work.ASGinzburgDraft.OrdinaryPerfectDerivedObject

/-! Original AS regularity gives homological smoothness of the actual cut
algebra. The actual regular enveloping module is represented by a bounded
finite projective cochain complex, with its actual augmentation. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v w
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutEnvelopingPerfectCochainComplex (hAS : A.ASRegular Q) :
    CochainComplex (ModuleCat.{v} (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))) ℤ :=
  (hAS.cutEnvelopingFiniteFourTermResolution A Q).perfectCochainComplex

theorem ASRegular.cutEnvelopingPerfectCochainComplex_term_finiteProjective
    (hAS : A.ASRegular Q) (i : ℤ) :
    ordinaryFiniteProjectiveProperty (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
      ((hAS.cutEnvelopingPerfectCochainComplex A Q).X i) :=
  (hAS.cutEnvelopingFiniteFourTermResolution A Q).perfectCochainComplex_term_finiteProjective i

theorem ASRegular.cutEnvelopingPerfectCochainComplex_term_finite
    (hAS : A.ASRegular Q) (i : ℤ) :
    Module.Finite (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
      ((hAS.cutEnvelopingPerfectCochainComplex A Q).X i) :=
  ((ordinaryFiniteProjectiveProperty_iff _ _).mp
    (hAS.cutEnvelopingPerfectCochainComplex_term_finiteProjective A Q i)).1

theorem ASRegular.cutEnvelopingPerfectCochainComplex_term_projective
    (hAS : A.ASRegular Q) (i : ℤ) :
    Projective ((hAS.cutEnvelopingPerfectCochainComplex A Q).X i) :=
  ((ordinaryFiniteProjectiveProperty_iff _ _).mp
    (hAS.cutEnvelopingPerfectCochainComplex_term_finiteProjective A Q i)).2

theorem ASRegular.cutEnvelopingPerfectCochainComplex_isZero_outside
    (hAS : A.ASRegular Q) (i : ℤ) (hi : i < -3 ∨ 0 < i) :
    IsZero ((hAS.cutEnvelopingPerfectCochainComplex A Q).X i) :=
  (hAS.cutEnvelopingFiniteFourTermResolution A Q).perfectCochainComplex_isZero_outside i hi

noncomputable def ASRegular.cutEnvelopingPerfectCochainAugmentation (hAS : A.ASRegular Q) :
    hAS.cutEnvelopingPerfectCochainComplex A Q ⟶
      (HomologicalComplex.single
        (ModuleCat (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))) (ComplexShape.up ℤ) 0).obj
        (regularEnvelopingModuleCat k (hAS.CutGradedAlgebra A Q)) :=
  (hAS.cutEnvelopingFiniteFourTermResolution A Q).perfectCochainAugmentation

instance ASRegular.cutEnvelopingPerfectCochainAugmentation_quasiIso (hAS : A.ASRegular Q) :
    QuasiIso (hAS.cutEnvelopingPerfectCochainAugmentation A Q) :=
  (hAS.cutEnvelopingFiniteFourTermResolution A Q).perfectCochainAugmentation_quasiIso

theorem ASRegular.cutHomologicallySmooth (hAS : A.ASRegular Q) :
    AlgebraHomologicallySmooth k (hAS.CutGradedAlgebra A Q) :=
  algebraHomologicallySmooth_of_finiteFourTermResolution k (hAS.CutGradedAlgebra A Q)
    (hAS.cutEnvelopingFiniteFourTermResolution A Q)

noncomputable def ASRegular.cutEnvelopingPerfectDerivedIso (hAS : A.ASRegular Q)
    [HasDerivedCategory.{w}
      (ModuleCat.{v} (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q)))] :
    DerivedCategory.Q.obj (hAS.cutEnvelopingPerfectCochainComplex A Q) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single
          (ModuleCat (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))) (ComplexShape.up ℤ) 0).obj
          (regularEnvelopingModuleCat k (hAS.CutGradedAlgebra A Q))) :=
  asIso (DerivedCategory.Q.map (hAS.cutEnvelopingPerfectCochainAugmentation A Q))

theorem ASRegular.cutRegularEnvelopingPerfectDerived (hAS : A.ASRegular Q)
    [HasDerivedCategory.{w}
      (ModuleCat.{v} (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q)))] :
    ordinaryPerfectDerivedProperty (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
      ((DerivedCategory.singleFunctor
        (ModuleCat (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))) 0).obj
        (regularEnvelopingModuleCat k (hAS.CutGradedAlgebra A Q))) :=
  ordinaryPerfectModuleProperty_derived_degree_zero
    (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
    (regularEnvelopingModuleCat k (hAS.CutGradedAlgebra A Q))
    (hAS.cutHomologicallySmooth A Q)

end ASGinzburg.ZAlgebra
