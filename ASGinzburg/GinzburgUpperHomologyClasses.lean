import ASGinzburg.GinzburgOriginalFilteredPrefixes
import ASGinzburg.GinzburgPrefixHomologyClasses
import ASGinzburg.GinzburgUpperProjectiveNaturality

/-! The actual upper homology/projective comparison reads the genuine
last-generator coefficient classes of any actual cycle representative. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgUpperProjectiveComponentIso_coefficients (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    (Q.ginzburgUpperProjectiveComponentIso k φ x v).hom ≫
      (((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientComponentEquiv Q v 0
        (Q.height x)).toModuleIso (g₂:=Pi.addCommGroup)).hom=
    HomologicalComplex.homologyMap
      (Q.ginzburgOriginalFilteredToPrefix k φ x.1 v.1 (v.2-x.2)) 0 ≫
        (Q.ginzburgPrefixTopFixedHomologyIso k φ x v 0).hom := by
  simp only [ginzburgUpperProjectiveComponentIso,ginzburgLayerProjectiveComponentIso,
    Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  change HomologicalComplex.homologyMap
      (Q.ginzburgFilteredToAssociatedGraded k φ x.1 v.1 0 (v.2-x.2)) 0 ≫
      HomologicalComplex.homologyMap
        (Q.ginzburgGeneratorPrefixGradedIso k φ x.1 v.1 0 (v.2-x.2)).inv 0 ≫
        (Q.ginzburgPrefixTopFixedHomologyIso k φ x v 0).hom=_
  rw [←HomologicalComplex.homologyMap_comp_assoc]
  rfl

theorem ginzburgUpperProjectiveComponentIso_class (φ : Q.Potential k)
    (x v : Q.LiftVertex)
    (z : Q.ginzburgGeneratorFiltrationAtDegree k x.1 v.1 0 0 (v.2-x.2))
    (hz : (Q.ginzburgGeneratorFilteredComplex k φ x.1 v.1 0 (v.2-x.2)).d 0 1 z=0) :
    (Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientComponentEquiv Q v 0
      (Q.height x) ((Q.ginzburgUpperProjectiveComponentIso k φ x v).hom
        (moduleCochainHomologyClass
          (Q.ginzburgGeneratorFilteredComplex k φ x.1 v.1 0 (v.2-x.2)) 0 z hz))=
      Q.ginzburgPrefixTopFixedUnrolledEquiv k φ x v 0
        (Submodule.Quotient.mk
          ((Q.ginzburgOriginalFilteredToPrefix k φ x.1 v.1 (v.2-x.2)).f 0 z)) := by
  let F := Q.ginzburgOriginalFilteredToPrefix k φ x.1 v.1 (v.2-x.2)
  have hf : (Q.ginzburgGeneratorPrefixComplex k φ x.1 v.1 0 (v.2-x.2)).d 0 1
      (F.f 0 z)=0 := by
    have he := congrArg (fun f => f z) (F.comm 0 1)
    simpa only [ModuleCat.comp_apply,hz,map_zero] using he
  change ((Q.ginzburgUpperProjectiveComponentIso k φ x v).hom ≫
    (((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientComponentEquiv Q v 0
      (Q.height x)).toModuleIso (g₂:=Pi.addCommGroup)).hom)
      (moduleCochainHomologyClass
        (Q.ginzburgGeneratorFilteredComplex k φ x.1 v.1 0 (v.2-x.2)) 0 z hz)=_
  rw [Q.ginzburgUpperProjectiveComponentIso_coefficients]
  change (Q.ginzburgPrefixTopFixedHomologyIso k φ x v 0).hom
    (HomologicalComplex.homologyMap F 0 (moduleCochainHomologyClass
      (Q.ginzburgGeneratorFilteredComplex k φ x.1 v.1 0 (v.2-x.2)) 0 z hz))=_
  rw [moduleCochainHomologyClass_naturality F 0 z hz hf]
  change Q.ginzburgPrefixTopFixedUnrolledEquiv k φ x v 0
    ((Q.ginzburgGeneratorPrefixTopHomologyQuotientIso k φ x.1 v.1 0 (v.2-x.2)).hom
      (moduleCochainHomologyClass
        (Q.ginzburgGeneratorPrefixComplex k φ x.1 v.1 0 (v.2-x.2)) 0 (F.f 0 z) hf))=_
  rw [Q.ginzburgPrefixTopHomologyQuotientIso_class]

end ASGinzburg.CutQuiver
