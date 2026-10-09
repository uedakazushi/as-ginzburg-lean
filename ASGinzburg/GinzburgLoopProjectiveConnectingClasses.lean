import ASGinzburg.GinzburgLoopDualClassFormula
import ASGinzburg.GinzburgLayerHomologyClasses
import ASGinzburg.GinzburgFilteredPrefixCoefficients
import ASGinzburg.GinzburgProjectiveConnectingMaps

/-! Actual degree minus two representatives determine the entire
native loop-to-dual projective differential through actual prefix classes. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgLoopCoefficientClass (φ : Q.Potential k)
    (x v : Q.LiftVertex)
    (f : Q.ginzburgGeneratorFiltrationAtDegree k x.1 v.1 (-2) (-2) (v.2-x.2)) :
    ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
      ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v (-2)) :=
  (Q.ginzburgLayerProjectiveComponentIso k φ x v (-2)).hom
    (moduleCochainHomologyClass
      (Q.ginzburgAssociatedGradedComplex k φ x.1 v.1 (-2) (v.2-x.2)) (-2)
      (Submodule.Quotient.mk f)
      (Q.ginzburgLoopLayerQuotient_cycle k φ x.1 v.1 (v.2-x.2) f))

noncomputable def ginzburgDualDifferentialCoefficients (φ : Q.Potential k)
    (x v : Q.LiftVertex)
    (f : Q.ginzburgGeneratorFiltrationAtDegree k x.1 v.1 (-2) (-2) (v.2-x.2)) :
    Π a : {a : Q.GinzburgArrow // a.target Q=v.1 ∧ a.cohomologicalDegree Q= -1},
      (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x)
        (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val)) :=
  Q.ginzburgPrefixTopFixedUnrolledEquiv k φ x v (-1)
    (Submodule.Quotient.mk
      ((Q.ginzburgFilteredToPrefix k φ x.1 v.1 (-1) (v.2-x.2)).f (-1)
        (Q.ginzburgLoopLayerDifferential k φ x.1 v.1 (v.2-x.2) f)))

set_option maxRecDepth 2000 in
theorem ginzburgLoopDualProjectiveComponent_class
    (φ : Q.Potential k) (x v : Q.LiftVertex)
    (f : Q.ginzburgGeneratorFiltrationAtDegree k x.1 v.1 (-2) (-2) (v.2-x.2)) :
    (Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientComponentEquiv Q v (-1)
      (Q.height x) (Q.ginzburgLoopDualProjectiveComponent k φ x v
        (Q.ginzburgLoopCoefficientClass k φ x v f))=
      Q.ginzburgDualDifferentialCoefficients k φ x v f := by
  let y := moduleCochainHomologyClass
    (Q.ginzburgAssociatedGradedComplex k φ x.1 v.1 (-2) (v.2-x.2)) (-2)
    (Submodule.Quotient.mk f) (Q.ginzburgLoopLayerQuotient_cycle k φ x.1 v.1 (v.2-x.2) f)
  let e := Q.ginzburgLayerProjectiveComponentIso k φ x v (-2)
  let dx := Q.ginzburgLoopLayerDifferential k φ x.1 v.1 (v.2-x.2) f
  have he : e.inv (e.hom y)=y := by
    change (e.hom ≫ e.inv) y=y
    rw [e.hom_inv_id]
    rfl
  have hy : Q.ginzburgGeneratorLoopToDualHomology k φ x.1 v.1 (v.2-x.2) y=
      moduleCochainHomologyClass
        (Q.ginzburgAssociatedGradedComplex k φ x.1 v.1 (-1) (v.2-x.2)) (-1)
        (Submodule.Quotient.mk dx) (Q.ginzburgDualLayerQuotient_cycle k φ x.1 v.1 (v.2-x.2) dx) :=
    Q.ginzburgLoopDualHomology_on_representative k φ x.1 v.1 (v.2-x.2) f
  change (Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientComponentEquiv Q v (-1)
    (Q.height x) ((Q.ginzburgLayerProjectiveComponentIso k φ x v (-1)).hom
      (Q.ginzburgGeneratorLoopToDualHomology k φ x.1 v.1 (v.2-x.2)
        (e.inv (e.hom y))))=_
  rw [he,hy]
  exact Q.ginzburgLayerProjectiveComponentIso_class k φ x v (-1) (Submodule.Quotient.mk dx)
    (Q.ginzburgDualLayerQuotient_cycle k φ x.1 v.1 (v.2-x.2) dx)

theorem ginzburgLoopDualProjectiveMap_class
    (φ : Q.Potential k) (x v : Q.LiftVertex)
    (f : Q.ginzburgGeneratorFiltrationAtDegree k x.1 v.1 (-2) (-2) (v.2-x.2)) :
    (Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientComponentEquiv Q v (-1)
      (Q.height x) (((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).map
        (Q.ginzburgLoopDualProjectiveMap k φ v)
          (Q.ginzburgLoopCoefficientClass k φ x v f))=
      Q.ginzburgDualDifferentialCoefficients k φ x v f := by
  rw [Q.ginzburgLoopDualProjectiveMap_component]
  exact Q.ginzburgLoopDualProjectiveComponent_class k φ x v f

end ASGinzburg.CutQuiver
