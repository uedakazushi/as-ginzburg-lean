import ASGinzburg.GinzburgProjectiveConnectingExactness
import ASGinzburg.GinzburgGeneratorLoopProjective

/-! Genuine connecting morphisms between the existing AS projective terms.
These constitute the left half, not a complete simple resolution. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgASProjectiveD₃ (φ : Q.Potential k) (v : Q.LiftVertex) :
    (Q.unrolledJacobianZAlgebra k φ).representable (Q.height (Q.tau.symm v)) ⟶
      (Q.unrolledJacobianZAlgebra k φ).asResolutionTerm₂ Q v :=
  ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorLoopTermIso Q v).inv ≫
    Q.ginzburgLoopDualProjectiveMap k φ v ≫
      ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorDualTermIso Q v).hom

noncomputable def ginzburgASProjectiveD₂ (φ : Q.Potential k) (v : Q.LiftVertex) :
    (Q.unrolledJacobianZAlgebra k φ).asResolutionTerm₂ Q v ⟶
      (Q.unrolledJacobianZAlgebra k φ).asResolutionTerm₁ Q v :=
  ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorDualTermIso Q v).inv ≫
    Q.ginzburgDualOriginalProjectiveMap k φ v ≫
      ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorOriginalTermIso Q v).hom

theorem ginzburgASProjectiveD₃_comp_D₂ (φ : Q.Potential k) (v : Q.LiftVertex) :
    Q.ginzburgASProjectiveD₃ k φ v ≫ Q.ginzburgASProjectiveD₂ k φ v = 0 := by
  simp only [ginzburgASProjectiveD₃,ginzburgASProjectiveD₂,Category.assoc,
    Iso.hom_inv_id_assoc]
  simp only [← Category.assoc,Q.ginzburgLoopDualProjectiveMap_comp,comp_zero,zero_comp]

noncomputable def ginzburgASProjectiveConnectingShortComplex (φ : Q.Potential k)
    (v : Q.LiftVertex) : ShortComplex (Q.unrolledJacobianZAlgebra k φ).RightModule :=
  ShortComplex.mk (Q.ginzburgASProjectiveD₃ k φ v) (Q.ginzburgASProjectiveD₂ k φ v)
    (Q.ginzburgASProjectiveD₃_comp_D₂ k φ v)

theorem GinzburgRegular.asProjectiveD₃_mono {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) :
    Mono (Q.ginzburgASProjectiveD₃ k φ v) := by
  unfold ginzburgASProjectiveD₃
  haveI := h.loopDualProjectiveMap_mono Q k v
  infer_instance

theorem GinzburgRegular.asProjectiveConnectingShortComplex_exact {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) :
    (Q.ginzburgASProjectiveConnectingShortComplex k φ v).Exact := by
  apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
    ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorLoopTermIso Q v)
    ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorDualTermIso Q v)
    ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorOriginalTermIso Q v)
    (S₁:=Q.ginzburgProjectiveConnectingShortComplex k φ v)
    (S₂:=Q.ginzburgASProjectiveConnectingShortComplex k φ v)
    (by simp [ginzburgProjectiveConnectingShortComplex,
      ginzburgASProjectiveConnectingShortComplex,ginzburgASProjectiveD₃])
    (by simp [ginzburgProjectiveConnectingShortComplex,
      ginzburgASProjectiveConnectingShortComplex,ginzburgASProjectiveD₂]))).mp
    (h.projectiveConnectingShortComplex_exact Q k v)

end ASGinzburg.CutQuiver
