import ASGinzburg.EndpointProjectiveMinimality
import ASGinzburg.GinzburgASProjectiveRadicalMaps

/-! The actual first and third Ginzburg AS differentials are minimal,
by their genuine radical factorization and unrolled endpoint heights.
The middle differential remains a separate proof obligation. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgASProjectiveD₁_minimal (φ : Q.Potential k) (v : Q.LiftVertex) :
    (Q.unrolledJacobianZAlgebra k φ).IsMinimalMorphism (Q.ginzburgASProjectiveD₁ k φ v) := by
  let A := Q.unrolledJacobianZAlgebra k φ
  apply A.isMinimalMorphism_comp_left
    (A.ginzburgGeneratorOriginalTermIso Q v).inv
  exact A.isMinimalMorphism_comp_left (Q.ginzburgOriginalRadicalProjectiveMap k φ v)
    (A.representableRadical (Q.height v)).inclusion
    (A.representableRadicalInclusion_minimal (Q.height v))

theorem ginzburgASProjectiveD₃_minimal (φ : Q.Potential k) (v : Q.LiftVertex) :
    (Q.unrolledJacobianZAlgebra k φ).IsMinimalMorphism (Q.ginzburgASProjectiveD₃ k φ v) :=
  (Q.unrolledJacobianZAlgebra k φ).representable_to_finiteCoproduct_minimal
    (Q.height (Q.tau.symm v))
    (fun a : Q.outgoingArrows (Q.tau.symm v) =>
      Q.height (Q.outgoingTarget (Q.tau.symm v) a))
    (fun a => Q.outgoingTarget_height_gt (Q.tau.symm v) a)
    (Q.ginzburgASProjectiveD₃ k φ v)

end ASGinzburg.CutQuiver
