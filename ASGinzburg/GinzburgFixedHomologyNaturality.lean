import ASGinzburg.GinzburgPrefixFixedFamilyAction
import ASGinzburg.GinzburgPrefixTopHomologyNaturality
import ASGinzburg.GinzburgLayerHomologyNaturality

/-! Actual prefix and associated-layer top homology comparisons with
fixed-endpoint A(Phi) components preserve genuine algebra precomposition. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgPrefixTopFixedHomologyIso (φ : Q.Potential k)
    (x v : Q.LiftVertex) (r : ℤ) :
    Q.ginzburgGeneratorPrefixHomology k φ x.1 v.1 r (v.2-x.2) r ≅
      ModuleCat.of k (Π a : {a : Q.GinzburgArrow // a.target Q=v.1 ∧ a.cohomologicalDegree Q=r},
        (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x)
          (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))) :=
  Q.ginzburgGeneratorPrefixTopHomologyQuotientIso k φ x.1 v.1 r (v.2-x.2) ≪≫
    (Q.ginzburgPrefixTopFixedUnrolledEquiv k φ x v r).toModuleIso (g₂:=Pi.addCommGroup)

theorem ginzburgPrefixTopFixedHomologyIso_left_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (r : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgPrefixLeftHomology k φ (v:=v) r r f ≫
        (Q.ginzburgPrefixTopFixedHomologyIso k φ x v r).hom=
      (Q.ginzburgPrefixTopFixedHomologyIso k φ y v r).hom ≫
        ModuleCat.ofHom (Q.ginzburgPrefixFixedFamilyPrecomposition k φ x y v r
          (Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x y (Submodule.Quotient.mk f))) := by
  have he : moduleCatShortComplexQuotientMap
        (Q.ginzburgPrefixTopShortComplexLeftMap k φ (v:=v) r f) ≫
        ((Q.ginzburgPrefixTopFixedUnrolledEquiv k φ x v r).toModuleIso (g₂:=Pi.addCommGroup)).hom=
      ((Q.ginzburgPrefixTopFixedUnrolledEquiv k φ y v r).toModuleIso (g₂:=Pi.addCommGroup)).hom ≫
        ModuleCat.ofHom (Q.ginzburgPrefixFixedFamilyPrecomposition k φ x y v r
          (Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x y (Submodule.Quotient.mk f))) := by
    apply ModuleCat.hom_ext
    exact Q.ginzburgPrefixTopFixedUnrolledEquiv_left_naturality k φ r f
  simp only [ginzburgPrefixTopFixedHomologyIso,Iso.trans_hom]
  rw [← Category.assoc,Q.ginzburgPrefixTopHomologyQuotientIso_left_naturality,
    Category.assoc,he,← Category.assoc]

noncomputable def ginzburgAssociatedTopFixedHomologyIso (φ : Q.Potential k)
    (x v : Q.LiftVertex) (r : ℤ) :
    Q.ginzburgAssociatedGradedHomology k φ x.1 v.1 r (v.2-x.2) r ≅
      ModuleCat.of k (Π a : {a : Q.GinzburgArrow // a.target Q=v.1 ∧ a.cohomologicalDegree Q=r},
        (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x)
          (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))) :=
  Q.ginzburgAssociatedGradedPrefixHomologyIso k φ x.1 v.1 r (v.2-x.2) r ≪≫
    Q.ginzburgPrefixTopFixedHomologyIso k φ x v r

theorem ginzburgAssociatedTopFixedHomologyIso_left_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (r : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgAssociatedLeftHomology k φ (v:=v) r r f ≫
        (Q.ginzburgAssociatedTopFixedHomologyIso k φ x v r).hom=
      (Q.ginzburgAssociatedTopFixedHomologyIso k φ y v r).hom ≫
        ModuleCat.ofHom (Q.ginzburgPrefixFixedFamilyPrecomposition k φ x y v r
          (Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x y (Submodule.Quotient.mk f))) := by
  simp only [ginzburgAssociatedTopFixedHomologyIso,Iso.trans_hom]
  rw [← Category.assoc,Q.ginzburgAssociatedPrefixHomologyIso_left_naturality,
    Category.assoc,Q.ginzburgPrefixTopFixedHomologyIso_left_naturality,← Category.assoc]

end ASGinzburg.CutQuiver
