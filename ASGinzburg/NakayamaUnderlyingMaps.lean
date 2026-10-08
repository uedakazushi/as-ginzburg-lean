import ASGinzburg.TruncatedCoverComponents
import ASGinzburg.NakayamaWindowProjectives
import ASGinzburg.NakayamaWindowComparisons
/-! Underlying Nakayama maps and the normalization equation in finite windows. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
@[reassoc] theorem rightFiniteWindowNakayamaRepresentableIso_hom_cover (hAS : A.ASRegular Q)
    (l r i : ℤ) (hli : l ≤ i) (hir : i ≤ r) :
    (A.rightFiniteWindowNakayamaRepresentableIso Q hAS l r i hli hir).hom ≫
        A.rightFiniteWindowRepresentableCover (l-Q.vertices) (r-Q.vertices) (i-Q.vertices)
          (sub_le_sub_right hli _) (sub_le_sub_right hir _) =
      A.rightFiniteWindowNakayamaRepresentableCover Q hAS l r i hli hir :=
  ASGinzburg.normalizedProjectiveIso_hom_comp _ _ _ _

noncomputable def rightFiniteDimensionalNakayamaUnderlyingMap (hAS : A.ASRegular Q)
    {M N : A.RightModule} (hM : A.rightFiniteDimensionalProperty M) (hN : A.rightFiniteDimensionalProperty N)
    (f : M ⟶ N) :
    A.rightFiniteDimensionalNakayamaUnderlying Q hAS M hM ⟶
      A.rightFiniteDimensionalNakayamaUnderlying Q hAS N hN :=
  (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor.map
    (show (⟨M,hM⟩ : A.RightFiniteDimensional) ⟶ ⟨N,hN⟩ from f)

theorem rightFiniteDimensionalNakayamaUnderlyingMap_comp (hAS : A.ASRegular Q)
    {M N P : A.RightModule} (hM : A.rightFiniteDimensionalProperty M)
    (hN : A.rightFiniteDimensionalProperty N) (hP : A.rightFiniteDimensionalProperty P)
    (f : M ⟶ N) (g : N ⟶ P) :
    A.rightFiniteDimensionalNakayamaUnderlyingMap Q hAS hM hP (f ≫ g) =
      A.rightFiniteDimensionalNakayamaUnderlyingMap Q hAS hM hN f ≫
        A.rightFiniteDimensionalNakayamaUnderlyingMap Q hAS hN hP g := by
  exact (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor.map_comp
    (show (⟨M,hM⟩ : A.RightFiniteDimensional) ⟶ ⟨N,hN⟩ from f)
    (show (⟨N,hN⟩ : A.RightFiniteDimensional) ⟶ ⟨P,hP⟩ from g)

end ASGinzburg.ZAlgebra
