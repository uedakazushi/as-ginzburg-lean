import ASGinzburg.GinzburgUpperHomologyRadical
import ASGinzburg.GinzburgDualOriginalRepresentatives
import ASGinzburg.GinzburgASProjectiveConnectingMaps

/-! The genuine middle differential is minimal, derived from the
original potential length condition and the actual connecting map.
No minimality or Ext conclusion is assumed. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgDualOriginalProjectiveComponent_mem_radical (φ : Q.Potential k)
    (x v : Q.LiftVertex)
    (y : ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
      ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v (-1))) :
    Q.ginzburgDualOriginalProjectiveComponent k φ x v y ∈
      (Q.unrolledJacobianZAlgebra k φ).positiveActionSpan
        ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v 0)
        (Q.height x) := by
  obtain ⟨z,hz,hlen,he⟩ := Q.ginzburgDualOriginalHomology_representative k φ x.1 v.1
    (v.2-x.2) ((Q.ginzburgLayerProjectiveComponentIso k φ x v (-1)).inv y)
  change (Q.ginzburgUpperProjectiveComponentIso k φ x v).hom
    (Q.ginzburgGeneratorDualToOriginalHomology k φ x.1 v.1 (v.2-x.2)
      ((Q.ginzburgLayerProjectiveComponentIso k φ x v (-1)).inv y)) ∈ _
  rw [he]
  exact Q.ginzburgUpperProjectiveComponentIso_class_mem_radical k φ x v z hz hlen

theorem ginzburgDualOriginalProjectiveMap_minimal (φ : Q.Potential k) (v : Q.LiftVertex) :
    (Q.unrolledJacobianZAlgebra k φ).IsMinimalMorphism
      (Q.ginzburgDualOriginalProjectiveMap k φ v) := by
  intro i y
  obtain ⟨x,rfl⟩ := Q.height_bijective.surjective i
  rw [Q.ginzburgDualOriginalProjectiveMap_component]
  exact Q.ginzburgDualOriginalProjectiveComponent_mem_radical k φ x v y

theorem ginzburgASProjectiveD₂_minimal (φ : Q.Potential k) (v : Q.LiftVertex) :
    (Q.unrolledJacobianZAlgebra k φ).IsMinimalMorphism
      (Q.ginzburgASProjectiveD₂ k φ v) := by
  let A := Q.unrolledJacobianZAlgebra k φ
  exact A.isMinimalMorphism_comp_left (A.ginzburgGeneratorDualTermIso Q v).inv _
    (A.isMinimalMorphism_comp_right (Q.ginzburgDualOriginalProjectiveMap k φ v)
      (A.ginzburgGeneratorOriginalTermIso Q v).hom
      (Q.ginzburgDualOriginalProjectiveMap_minimal k φ v))

end ASGinzburg.CutQuiver
