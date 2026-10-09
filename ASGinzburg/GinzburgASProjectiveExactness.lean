import ASGinzburg.GinzburgASProjectiveRadicalMaps
import ASGinzburg.GinzburgProjectiveRepresentableExactness

/-! Genuine right-module exactness at the right two existing AS terms.
Together with regularity at the left terms this gives an actual exact
four-term projective complex, without yet proving minimality or Ext duality. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgASProjectiveDualOriginalShortComplex_exact (φ : Q.Potential k)
    (v : Q.LiftVertex) :
    (Q.ginzburgASProjectiveDualOriginalShortComplex k φ v).Exact := by
  apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
    ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorDualTermIso Q v)
    ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorOriginalTermIso Q v)
    (Iso.refl _)
    (S₁:=Q.ginzburgProjectiveDualOriginalShortComplex k φ v)
    (S₂:=Q.ginzburgASProjectiveDualOriginalShortComplex k φ v)
    (by simp [ginzburgProjectiveDualOriginalShortComplex,
      ginzburgASProjectiveDualOriginalShortComplex,ginzburgASProjectiveD₂])
    (by simp [ginzburgProjectiveDualOriginalShortComplex,
      ginzburgASProjectiveDualOriginalShortComplex,ginzburgASProjectiveD₁]))).mp
    (Q.ginzburgProjectiveDualOriginalShortComplex_exact k φ v)

theorem ginzburgASProjectiveOriginalSimpleShortComplex_exact (φ : Q.Potential k)
    (v : Q.LiftVertex) :
    (Q.ginzburgASProjectiveOriginalSimpleShortComplex k φ v).Exact := by
  apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
    ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorOriginalTermIso Q v)
    (Iso.refl _) (Iso.refl _)
    (S₁:=Q.ginzburgProjectiveOriginalSimpleShortComplex k φ v)
    (S₂:=Q.ginzburgASProjectiveOriginalSimpleShortComplex k φ v)
    (by simp [ginzburgProjectiveOriginalSimpleShortComplex,
      ginzburgASProjectiveOriginalSimpleShortComplex,ginzburgASProjectiveD₁])
    (by simp [ginzburgProjectiveOriginalSimpleShortComplex,
      ginzburgASProjectiveOriginalSimpleShortComplex]))).mp
    (Q.ginzburgProjectiveOriginalSimpleShortComplex_exact k φ v)

end ASGinzburg.CutQuiver
