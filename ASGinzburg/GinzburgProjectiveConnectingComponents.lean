import ASGinzburg.GinzburgUpperProjectiveNaturality
import ASGinzburg.IsoTransportNaturality

/-! The intrinsic homology connecting maps become genuine linear
components between the actual projective generator modules and commute
with actual degree-zero path classes. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgLoopDualProjectiveComponent (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v (-2)) ⟶
      ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v (-1)) :=
  (Q.ginzburgLayerProjectiveComponentIso k φ x v (-2)).inv ≫
    Q.ginzburgGeneratorLoopToDualHomology k φ x.1 v.1 (v.2-x.2) ≫
      (Q.ginzburgLayerProjectiveComponentIso k φ x v (-1)).hom

noncomputable def ginzburgDualOriginalProjectiveComponent (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v (-1)) ⟶
      ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v 0) :=
  (Q.ginzburgLayerProjectiveComponentIso k φ x v (-1)).inv ≫
    Q.ginzburgGeneratorDualToOriginalHomology k φ x.1 v.1 (v.2-x.2) ≫
      (Q.ginzburgUpperProjectiveComponentIso k φ x v).hom

theorem ginzburgLoopDualProjectiveComponent_left_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex}
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v (-2)).obj.map
        (show (⟨Q.height x⟩ : (Q.unrolledJacobianZAlgebra k φ).Obj) ⟶ ⟨Q.height y⟩ from
          Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x y (Submodule.Quotient.mk f)).op ≫
        Q.ginzburgLoopDualProjectiveComponent k φ x v=
      Q.ginzburgLoopDualProjectiveComponent k φ y v ≫
        ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v (-1)).obj.map
          (show (⟨Q.height x⟩ : (Q.unrolledJacobianZAlgebra k φ).Obj) ⟶ ⟨Q.height y⟩ from
            Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x y (Submodule.Quotient.mk f)).op := by
  unfold ginzburgLoopDualProjectiveComponent
  exact isoTransport_naturality
    (Q.ginzburgLayerProjectiveComponentIso k φ x v (-2))
    (Q.ginzburgLayerProjectiveComponentIso k φ y v (-2))
    (Q.ginzburgLayerProjectiveComponentIso k φ x v (-1))
    (Q.ginzburgLayerProjectiveComponentIso k φ y v (-1)) _ _ _ _ _ _
    (Q.ginzburgLayerProjectiveComponentIso_left_naturality k φ (-2) f).symm
    (Q.ginzburgLayerProjectiveComponentIso_left_naturality k φ (-1) f).symm
    (Q.ginzburgLoopToDualHomology_left_naturality k φ f)

theorem ginzburgDualOriginalProjectiveComponent_left_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex}
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v (-1)).obj.map
        (show (⟨Q.height x⟩ : (Q.unrolledJacobianZAlgebra k φ).Obj) ⟶ ⟨Q.height y⟩ from
          Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x y (Submodule.Quotient.mk f)).op ≫
        Q.ginzburgDualOriginalProjectiveComponent k φ x v=
      Q.ginzburgDualOriginalProjectiveComponent k φ y v ≫
        ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v 0).obj.map
          (show (⟨Q.height x⟩ : (Q.unrolledJacobianZAlgebra k φ).Obj) ⟶ ⟨Q.height y⟩ from
            Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x y (Submodule.Quotient.mk f)).op := by
  unfold ginzburgDualOriginalProjectiveComponent
  exact isoTransport_naturality
    (Q.ginzburgLayerProjectiveComponentIso k φ x v (-1))
    (Q.ginzburgLayerProjectiveComponentIso k φ y v (-1))
    (Q.ginzburgUpperProjectiveComponentIso k φ x v)
    (Q.ginzburgUpperProjectiveComponentIso k φ y v) _ _ _ _ _ _
    (Q.ginzburgLayerProjectiveComponentIso_left_naturality k φ (-1) f).symm
    (Q.ginzburgUpperProjectiveComponentIso_left_naturality k φ f).symm
    (Q.ginzburgDualToOriginalHomology_left_naturality k φ f)

end ASGinzburg.CutQuiver
