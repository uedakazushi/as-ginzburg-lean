import work.ASGinzburgDraft.GinzburgNativeASPresentation
import work.ASGinzburgDraft.NativeCutDerivativeMinimalRelationClasses
import work.ASGinzburgDraft.LinearIdealExtensionality
import ASGinzburg.ASFoundationMinimalRelationBasis
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-! Original Ginzburg regularity makes the literal cut-derivative classes
a genuine basis of the native Jacobian minimal relation quotient. -/
namespace ASGinzburg.CutQuiver
open ZAlgebra
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem GinzburgRegular.nativePathPresentation_kernelIdeal {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) :
    ((Q.unrolledJacobianZAlgebra k φ).unrolledPathPresentation Q
      (fun w => h.minimalASResolution Q k w)).kernel = Q.unrolledJacobianIdeal k φ :=
  LinearIdeal.eq_of_hom_eq _ _ (h.nativePathPresentation_kernel Q k)

set_option synthInstance.maxHeartbeats 200000 in
theorem GinzburgRegular.nativeMinimalRelation_finrank {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (i j : Q.Vertex) :
    Module.finrank k (Q.MinimalRelationComponent (Q.unrolledJacobianIdeal k φ)
      (i.val : ℤ) (j.val : ℤ)) = Fintype.card (Q.FoundationRelationArrow i j) := by
  have hc := (Q.unrolledJacobianZAlgebra k φ).foundationMinimalRelation_finrank Q
    (fun w => h.minimalASResolution Q k w) i j
  rw [h.nativePathPresentation_kernelIdeal Q k] at hc
  exact hc

set_option synthInstance.maxHeartbeats 200000 in
noncomputable def GinzburgRegular.foundationCutDerivativeMinimalRelationBasis
    {φ : Q.Potential k} (h : Q.GinzburgRegular k φ) (i j : Q.Vertex) :
    Module.Basis (Q.FoundationRelationArrow i j) k
      (Q.MinimalRelationComponent (Q.unrolledJacobianIdeal k φ) (i.val : ℤ) (j.val : ℤ)) :=
  basisOfTopLeSpanOfCardEqFinrank (Q.foundationMinimalCutDerivativeClass k φ i j)
    (by rw [Q.foundationMinimalCutDerivativeClass_span])
    (h.nativeMinimalRelation_finrank Q k i j).symm

set_option synthInstance.maxHeartbeats 200000 in
theorem GinzburgRegular.foundationCutDerivativeMinimalRelationBasis_apply
    {φ : Q.Potential k} (h : Q.GinzburgRegular k φ) (i j : Q.Vertex)
    (a : Q.FoundationRelationArrow i j) :
    h.foundationCutDerivativeMinimalRelationBasis Q k i j a =
      Q.foundationMinimalCutDerivativeClass k φ i j a := by
  exact congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) a

set_option synthInstance.maxHeartbeats 200000 in
theorem GinzburgRegular.foundationMinimalCutDerivativeClass_linearIndependent
    {φ : Q.Potential k} (h : Q.GinzburgRegular k φ) (i j : Q.Vertex) :
    LinearIndependent k (Q.foundationMinimalCutDerivativeClass k φ i j) :=
  linearIndependent_of_top_le_span_of_card_eq_finrank
    (by rw [Q.foundationMinimalCutDerivativeClass_span])
    (h.nativeMinimalRelation_finrank Q k i j).symm

end ASGinzburg.CutQuiver
