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
  A.rightFiniteDimensionalProperty.ι.mapIso
    ((A.rightFiniteWindowProperty (l-Q.vertices) (r-Q.vertices)).ι.mapIso
      (A.rightFiniteWindowNakayamaRepresentableIso Q hAS l r i hli hir))

end ASGinzburg.ZAlgebra
