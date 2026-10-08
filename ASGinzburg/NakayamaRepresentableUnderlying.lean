import ASGinzburg.NakayamaUnderlyingMaps
/-! The normalized finite-window projective-cover isomorphism as an actual
morphism of the original right-module category. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
noncomputable def rightFiniteWindowNakayamaRepresentableModuleIso (hAS : A.ASRegular Q)
    (l r i : ℤ) (hli : l ≤ i) (hir : i ≤ r) :
    A.rightFiniteDimensionalNakayamaUnderlying Q hAS (A.rightTruncatedRepresentable l i)
        (A.rightTruncatedRepresentable_finite l i) ≅
      A.rightTruncatedRepresentable (l-Q.vertices) (i-Q.vertices) :=
  { hom := (A.rightFiniteWindowNakayamaRepresentableIso Q hAS l r i hli hir).hom
    inv := (A.rightFiniteWindowNakayamaRepresentableIso Q hAS l r i hli hir).inv
    hom_inv_id := (A.rightFiniteWindowNakayamaRepresentableIso Q hAS l r i hli hir).hom_inv_id
    inv_hom_id := (A.rightFiniteWindowNakayamaRepresentableIso Q hAS l r i hli hir).inv_hom_id }

end ASGinzburg.ZAlgebra
