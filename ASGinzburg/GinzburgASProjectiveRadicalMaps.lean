import ASGinzburg.GinzburgProjectiveRadicalExactness
import ASGinzburg.GinzburgASProjectiveConnectingMaps

/-! The genuine rightmost AS-term differential into the existing
representable and its actual simple quotient. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgASProjectiveD₁ (φ : Q.Potential k) (v : Q.LiftVertex) :
    (Q.unrolledJacobianZAlgebra k φ).asResolutionTerm₁ Q v ⟶
      (Q.unrolledJacobianZAlgebra k φ).representable (Q.height v) :=
  ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorOriginalTermIso Q v).inv ≫
    Q.ginzburgOriginalRepresentableProjectiveMap k φ v

theorem ginzburgASProjectiveD₂_comp_D₁ (φ : Q.Potential k) (v : Q.LiftVertex) :
    Q.ginzburgASProjectiveD₂ k φ v ≫ Q.ginzburgASProjectiveD₁ k φ v=0 := by
  simp only [ginzburgASProjectiveD₂,ginzburgASProjectiveD₁,Category.assoc,
    Iso.hom_inv_id_assoc]
  simp only [Q.ginzburgDualOriginalProjectiveMap_comp_representable,comp_zero]

theorem ginzburgASProjectiveD₁_comp_simpleπ (φ : Q.Potential k) (v : Q.LiftVertex) :
    Q.ginzburgASProjectiveD₁ k φ v ≫
      (Q.unrolledJacobianZAlgebra k φ).simpleRightModuleπ (Q.height v)=0 := by
  rw [ginzburgASProjectiveD₁,Category.assoc,
    ginzburgOriginalRepresentableProjectiveMap_comp_simpleπ,comp_zero]

noncomputable def ginzburgASProjectiveDualOriginalShortComplex (φ : Q.Potential k)
    (v : Q.LiftVertex) : ShortComplex (Q.unrolledJacobianZAlgebra k φ).RightModule :=
  ShortComplex.mk (Q.ginzburgASProjectiveD₂ k φ v) (Q.ginzburgASProjectiveD₁ k φ v)
    (Q.ginzburgASProjectiveD₂_comp_D₁ k φ v)

noncomputable def ginzburgASProjectiveOriginalSimpleShortComplex (φ : Q.Potential k)
    (v : Q.LiftVertex) : ShortComplex (Q.unrolledJacobianZAlgebra k φ).RightModule :=
  ShortComplex.mk (Q.ginzburgASProjectiveD₁ k φ v)
    ((Q.unrolledJacobianZAlgebra k φ).simpleRightModuleπ (Q.height v))
    (Q.ginzburgASProjectiveD₁_comp_simpleπ k φ v)

end ASGinzburg.CutQuiver
