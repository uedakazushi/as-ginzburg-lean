import ASGinzburg.GinzburgAugmentationRadicalNaturality
import ASGinzburg.GinzburgProjectiveConnectingComponents

/-! The intrinsic augmentation homology map gives actual components
from the original-generator projective module to the existing radical. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgOriginalRadicalProjectiveComponent (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v 0) ⟶
      ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).representableRadical (Q.height v)).object :=
  (Q.ginzburgUpperProjectiveComponentIso k φ x v).inv ≫
    Q.ginzburgGeneratorFiltrationRadicalMap k φ x.1 v.1 (v.2-x.2) ≫
      (Q.ginzburgAugmentationRadicalComponentIso k φ x v).hom

theorem ginzburgOriginalRadicalProjectiveComponent_left_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex}
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v 0).obj.map
        (show (⟨Q.height x⟩ : (Q.unrolledJacobianZAlgebra k φ).Obj) ⟶ ⟨Q.height y⟩ from
          Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x y (Submodule.Quotient.mk f)).op ≫
        Q.ginzburgOriginalRadicalProjectiveComponent k φ x v=
      Q.ginzburgOriginalRadicalProjectiveComponent k φ y v ≫
        ((Q.unrolledJacobianZAlgebra k φ).representableRadical (Q.height v)).object.obj.map
          (show (⟨Q.height x⟩ : (Q.unrolledJacobianZAlgebra k φ).Obj) ⟶ ⟨Q.height y⟩ from
            Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x y (Submodule.Quotient.mk f)).op := by
  unfold ginzburgOriginalRadicalProjectiveComponent
  exact isoTransport_naturality
    (Q.ginzburgUpperProjectiveComponentIso k φ x v)
    (Q.ginzburgUpperProjectiveComponentIso k φ y v)
    (Q.ginzburgAugmentationRadicalComponentIso k φ x v)
    (Q.ginzburgAugmentationRadicalComponentIso k φ y v) _ _ _ _ _ _
    (Q.ginzburgUpperProjectiveComponentIso_left_naturality k φ f).symm
    (Q.ginzburgAugmentationRadicalComponentIso_left_naturality k φ f).symm
    (Q.ginzburgFiltrationRadicalMap_left_naturality k φ f).symm

theorem ginzburgOriginalRadicalProjectiveComponent_epi (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    Epi (Q.ginzburgOriginalRadicalProjectiveComponent k φ x v) := by
  unfold ginzburgOriginalRadicalProjectiveComponent
  haveI := Q.ginzburgGeneratorFiltrationRadicalMap_epi k φ x.1 v.1 (v.2-x.2)
  infer_instance

theorem ginzburgDualOriginalProjectiveComponent_comp_radical (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    Q.ginzburgDualOriginalProjectiveComponent k φ x v ≫
      Q.ginzburgOriginalRadicalProjectiveComponent k φ x v=0 := by
  simp only [ginzburgDualOriginalProjectiveComponent,ginzburgOriginalRadicalProjectiveComponent,
    Category.assoc,Iso.hom_inv_id_assoc]
  simp only [← Category.assoc,Q.ginzburgGeneratorDualToOriginalHomology_comp,comp_zero,zero_comp]

noncomputable def ginzburgProjectiveDualRadicalComponentShortComplex (φ : Q.Potential k)
    (x v : Q.LiftVertex) : ShortComplex (ModuleCat.{u} k) :=
  ShortComplex.mk (Q.ginzburgDualOriginalProjectiveComponent k φ x v)
    (Q.ginzburgOriginalRadicalProjectiveComponent k φ x v)
    (Q.ginzburgDualOriginalProjectiveComponent_comp_radical k φ x v)

theorem ginzburgProjectiveDualRadicalComponentShortComplex_exact (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    (Q.ginzburgProjectiveDualRadicalComponentShortComplex k φ x v).Exact := by
  apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
    (Q.ginzburgLayerProjectiveComponentIso k φ x v (-1))
    (Q.ginzburgUpperProjectiveComponentIso k φ x v)
    (Q.ginzburgAugmentationRadicalComponentIso k φ x v)
    (S₁:=Q.ginzburgGeneratorDualOriginalShortComplex k φ x.1 v.1 (v.2-x.2))
    (S₂:=Q.ginzburgProjectiveDualRadicalComponentShortComplex k φ x v)
    (by simp [ginzburgGeneratorDualOriginalShortComplex,
      ginzburgProjectiveDualRadicalComponentShortComplex,ginzburgDualOriginalProjectiveComponent])
    (by simp [ginzburgGeneratorDualOriginalShortComplex,
      ginzburgProjectiveDualRadicalComponentShortComplex,ginzburgOriginalRadicalProjectiveComponent]))).mp
    (Q.ginzburgGeneratorDualOriginalShortComplex_exact k φ x.1 v.1 (v.2-x.2))

end ASGinzburg.CutQuiver
