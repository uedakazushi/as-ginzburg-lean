import ASGinzburg.GinzburgFirstProjectiveHomologyMap
import ASGinzburg.GinzburgCutCochainClasses
import ASGinzburg.GinzburgOriginalUnitProjectiveClasses
import ASGinzburg.GinzburgProjectiveRadicalExactness

/-! The genuine native first projective map sends actual filtered
cycle representatives to their actual degree-zero Jacobian classes. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgOriginalFilteredCutMap (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    Q.ginzburgGeneratorFilteredComplex k φ x.1 v.1 0 (v.2-x.2) ⟶
      Q.ginzburgCutCochainComplex k φ x.1 v.1 (v.2-x.2) :=
  Q.ginzburgGeneratorFilteredAugmentationInclusion k φ x.1 v.1 0 (v.2-x.2) ≫
    Q.ginzburgAugmentationCochainInclusion k φ x.1 v.1 (v.2-x.2)

theorem ginzburgOriginalRepresentableProjectiveMap_homology_component
    (φ : Q.Potential k) (x v : Q.LiftVertex) (hx : Q.height x<Q.height v) :
    ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).map
      (Q.ginzburgOriginalRepresentableProjectiveMap k φ v)=
      (Q.ginzburgUpperProjectiveComponentIso k φ x v).inv ≫
        HomologicalComplex.homologyMap (Q.ginzburgOriginalFilteredCutMap k φ x v) 0 ≫
          (Q.ginzburgCutHomologyZeroUnrolledIso k φ x v).hom := by
  rw [ginzburgOriginalRepresentableProjectiveMap,Functor.map_comp,
    Q.ginzburgOriginalRadicalProjectiveMap_component]
  simp only [ginzburgOriginalRadicalProjectiveComponent,Category.assoc]
  rw [Q.ginzburgAugmentationRadicalComponentIso_hom_inclusion k φ x v hx]
  rw [←Category.assoc
    (Q.ginzburgGeneratorFiltrationRadicalMap k φ x.1 v.1 (v.2-x.2))
    (Q.ginzburgAugmentationHeightHomologyIso k φ x v hx 0).hom
    (Q.ginzburgCutHomologyZeroUnrolledIso k φ x v).hom]
  rw [Q.ginzburgGeneratorFiltrationRadicalMap_cut]
  rfl

theorem ginzburgOriginalFilteredCutMap_cycle (φ : Q.Potential k)
    (x v : Q.LiftVertex)
    (f : Q.ginzburgGeneratorFiltrationAtDegree k x.1 v.1 0 0 (v.2-x.2)) :
    (Q.ginzburgCutCochainComplex k φ x.1 v.1 (v.2-x.2)).d 0 1
      ((Q.ginzburgOriginalFilteredCutMap k φ x v).f 0 f)=0 := by
  have h := congrArg (fun g => g f) ((Q.ginzburgOriginalFilteredCutMap k φ x v).comm 0 1)
  simpa only [ModuleCat.comp_apply,Q.ginzburgOriginalFiltered_cycle,map_zero] using h

set_option maxRecDepth 2048 in
theorem ginzburgOriginalRepresentableProjectiveMap_class
    (φ : Q.Potential k) (x v : Q.LiftVertex) (hx : Q.height x<Q.height v)
    (f : Q.ginzburgGeneratorFiltrationAtDegree k x.1 v.1 0 0 (v.2-x.2)) :
    ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).map
      (Q.ginzburgOriginalRepresentableProjectiveMap k φ v)
      ((Q.ginzburgUpperProjectiveComponentIso k φ x v).hom
        (moduleCochainHomologyClass
          (Q.ginzburgGeneratorFilteredComplex k φ x.1 v.1 0 (v.2-x.2)) 0 f
          (Q.ginzburgOriginalFiltered_cycle k φ x v f)))=
      Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x v
        (Submodule.Quotient.mk ((Q.ginzburgOriginalFilteredCutMap k φ x v).f 0 f)) := by
  let y := moduleCochainHomologyClass
    (Q.ginzburgGeneratorFilteredComplex k φ x.1 v.1 0 (v.2-x.2)) 0 f
    (Q.ginzburgOriginalFiltered_cycle k φ x v f)
  let e := Q.ginzburgUpperProjectiveComponentIso k φ x v
  have he : e.inv (e.hom y)=y := by
    change (e.hom ≫ e.inv) y=y
    rw [e.hom_inv_id]
    rfl
  rw [Q.ginzburgOriginalRepresentableProjectiveMap_homology_component k φ x v hx]
  change (Q.ginzburgCutHomologyZeroUnrolledIso k φ x v).hom
    (HomologicalComplex.homologyMap (Q.ginzburgOriginalFilteredCutMap k φ x v) 0
      (e.inv (e.hom y)))=_
  rw [he]
  rw [moduleCochainHomologyClass_naturality (Q.ginzburgOriginalFilteredCutMap k φ x v) 0 f
    (Q.ginzburgOriginalFiltered_cycle k φ x v f) (Q.ginzburgOriginalFilteredCutMap_cycle k φ x v f)]
  change Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x v
    ((Q.ginzburgCutHomologyZeroQuotientIso k φ x.1 v.1 (v.2-x.2)).hom
      (moduleCochainHomologyClass
        (Q.ginzburgCutCochainComplex k φ x.1 v.1 (v.2-x.2)) 0
        ((Q.ginzburgOriginalFilteredCutMap k φ x v).f 0 f)
        (Q.ginzburgOriginalFilteredCutMap_cycle k φ x v f)))=_
  rw [Q.ginzburgCutHomologyZeroQuotientIso_cochain_class]

end ASGinzburg.CutQuiver
