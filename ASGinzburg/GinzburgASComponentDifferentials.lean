import ASGinzburg.GinzburgAugmentationRadical
import ASGinzburg.GinzburgProjectiveTermComponents
import ASGinzburg.GinzburgGeneratorHomologyComplex

/-! Transport the intrinsic filtration homology maps to the actual
evaluation components of the existing AS terms. Module naturality remains
a separate proof obligation. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgASComponentD₃ (φ : Q.Potential k) (x v : Q.LiftVertex) :
    ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).representable (Q.height (Q.tau.symm v))) ⟶
      ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).asResolutionTerm₂ Q v) :=
  (Q.ginzburgLoopLayerHomologyRepresentableIso k φ x v).inv ≫
    Q.ginzburgGeneratorLoopToDualHomology k φ x.1 v.1 (v.2-x.2) ≫
      (Q.ginzburgDualLayerHomologyTermTwoIso k φ x v).hom

noncomputable def ginzburgASComponentD₂ (φ : Q.Potential k) (x v : Q.LiftVertex) :
    ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).asResolutionTerm₂ Q v) ⟶
      ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).asResolutionTerm₁ Q v) :=
  (Q.ginzburgDualLayerHomologyTermTwoIso k φ x v).inv ≫
    Q.ginzburgGeneratorDualToOriginalHomology k φ x.1 v.1 (v.2-x.2) ≫
      (Q.ginzburgUpperFilteredHomologyTermOneIso k φ x v).hom

noncomputable def ginzburgASComponentRadicalMap (φ : Q.Potential k) (x v : Q.LiftVertex) :
    ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).asResolutionTerm₁ Q v) ⟶
      ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).representableRadical (Q.height v)).object :=
  (Q.ginzburgUpperFilteredHomologyTermOneIso k φ x v).inv ≫
    Q.ginzburgGeneratorFiltrationRadicalMap k φ x.1 v.1 (v.2-x.2) ≫
      (Q.ginzburgAugmentationRadicalComponentIso k φ x v).hom

noncomputable def ginzburgASComponentD₁ (φ : Q.Potential k) (x v : Q.LiftVertex) :
    ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).asResolutionTerm₁ Q v) ⟶
      ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).representable (Q.height v)) :=
  Q.ginzburgASComponentRadicalMap k φ x v ≫
    ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).map
      ((Q.unrolledJacobianZAlgebra k φ).representableRadical (Q.height v)).inclusion

theorem ginzburgASComponentD₃_comp_D₂ (φ : Q.Potential k) (x v : Q.LiftVertex) :
    Q.ginzburgASComponentD₃ k φ x v ≫ Q.ginzburgASComponentD₂ k φ x v=0 := by
  simp only [ginzburgASComponentD₃,ginzburgASComponentD₂,Category.assoc,
    Iso.hom_inv_id_assoc]
  simp only [← Category.assoc,Q.ginzburgGeneratorLoopDualOriginal_comp,comp_zero,zero_comp]

theorem ginzburgASComponentD₂_comp_radicalMap (φ : Q.Potential k) (x v : Q.LiftVertex) :
    Q.ginzburgASComponentD₂ k φ x v ≫ Q.ginzburgASComponentRadicalMap k φ x v=0 := by
  simp only [ginzburgASComponentD₂,ginzburgASComponentRadicalMap,Category.assoc,
    Iso.hom_inv_id_assoc]
  simp only [← Category.assoc,Q.ginzburgGeneratorDualToOriginalHomology_comp,comp_zero,zero_comp]

theorem ginzburgASComponentD₂_comp_D₁ (φ : Q.Potential k) (x v : Q.LiftVertex) :
    Q.ginzburgASComponentD₂ k φ x v ≫ Q.ginzburgASComponentD₁ k φ x v=0 := by
  rw [ginzburgASComponentD₁,← Category.assoc,Q.ginzburgASComponentD₂_comp_radicalMap,
    zero_comp]

theorem ginzburgASComponentD₁_comp_simpleπ (φ : Q.Potential k) (x v : Q.LiftVertex) :
    Q.ginzburgASComponentD₁ k φ x v ≫
      ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).map
        ((Q.unrolledJacobianZAlgebra k φ).simpleRightModuleπ (Q.height v))=0 := by
  rw [ginzburgASComponentD₁,Category.assoc,← Functor.map_comp]
  simp only [ZAlgebra.simpleRightModuleπ,ZAlgebra.RightSubmodule.quotientπ,
    cokernel.condition,Functor.map_zero,comp_zero]

theorem ginzburgASComponentRadicalMap_epi (φ : Q.Potential k) (x v : Q.LiftVertex) :
    Epi (Q.ginzburgASComponentRadicalMap k φ x v) := by
  letI := Q.ginzburgGeneratorFiltrationRadicalMap_epi k φ x.1 v.1 (v.2-x.2)
  unfold ginzburgASComponentRadicalMap
  infer_instance

theorem GinzburgRegular.asComponentD₃_mono {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (x v : Q.LiftVertex) :
    Mono (Q.ginzburgASComponentD₃ k φ x v) := by
  letI := h.loopToDualHomology_mono Q k x.1 v.1 (v.2-x.2)
  unfold ginzburgASComponentD₃
  infer_instance

end ASGinzburg.CutQuiver
