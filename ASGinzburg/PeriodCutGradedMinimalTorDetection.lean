import ASGinzburg.PeriodCutMinimalTorDetection
import ASGinzburg.PeriodCutGradedForgetExactness
import ASGinzburg.PeriodCutGradedForgetPreservation
import ASGinzburg.PeriodCutOrdinaryMinimality
import ASGinzburg.MapProjectiveResolutionOfTerms

/-! A genuine graded projective resolution, with genuinely projective forgotten
terms and native radical-minimal differentials, detects its bounded-below
terms by actual ordinary Tor. No existence of minimal resolutions is assumed
as a conclusion of this criterion. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cutGradedMinimalResolution_ordinary_term_isZero_of_tor
    {M : E.CutGradedRightModule Q} (P : ProjectiveResolution M)
    (hMinimal : ∀ i j, CutGradedRightModule.IsMinimalMorphism (P.complex.d i j))
    (n : ℕ) (b : ℤ)
    (hb : ∀ q : ℤ, q < b → (P.complex.X n).grade q = ⊥)
    (hTor : IsZero ((balancedTensorTorLeftFunctor k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q) n).obj M.ringModule)) :
    IsZero ((E.cutGradedForgetFunctor Q).obj (P.complex.X n)) := by
  let U := mapProjectiveResolutionOfTerms (E.cutGradedForgetFunctor Q) P (fun _ => inferInstance)
  exact E.cutMinimalProjectiveResolution_term_isZero_of_tor Q M.ringModule U n
    (P.complex.X n) (Iso.refl _) b hb
    (by
      intro i j x
      exact E.cutGradedMinimalMorphism_ordinary_actionSpan Q
        (P.complex.d i j) (hMinimal i j) x) hTor

theorem cutGradedMinimalResolution_term_isZero_of_tor
    {M : E.CutGradedRightModule Q} (P : ProjectiveResolution M)
    (hMinimal : ∀ i j, CutGradedRightModule.IsMinimalMorphism (P.complex.d i j))
    (n : ℕ) (b : ℤ)
    (hb : ∀ q : ℤ, q < b → (P.complex.X n).grade q = ⊥)
    (hTor : IsZero ((balancedTensorTorLeftFunctor k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q) n).obj M.ringModule)) :
    IsZero (P.complex.X n) := by
  have hz := E.cutGradedMinimalResolution_ordinary_term_isZero_of_tor Q
    P hMinimal n b hb hTor
  have hs : Subsingleton ((E.cutGradedForgetFunctor Q).obj (P.complex.X n)) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  letI : Subsingleton (P.complex.X n).space := hs
  apply (IsZero.iff_id_eq_zero (P.complex.X n)).mpr
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim _ _

theorem cutGradedMinimalResolution_ordinary_hasProjectiveDimensionLE_of_tor_four
    {M : E.CutGradedRightModule Q} (P : ProjectiveResolution M)
    (hMinimal : ∀ i j, CutGradedRightModule.IsMinimalMorphism (P.complex.d i j))
    (b : ℤ) (hb : ∀ q : ℤ, q < b → (P.complex.X 4).grade q = ⊥)
    (hTor : IsZero ((balancedTensorTorLeftFunctor k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q) 4).obj M.ringModule)) :
    HasProjectiveDimensionLE M.ringModule 3 :=
  fourTermProjectiveResolution_hasProjectiveDimensionLE
    (mapProjectiveResolutionOfTerms (E.cutGradedForgetFunctor Q) P (fun _ => inferInstance))
    (E.cutGradedMinimalResolution_ordinary_term_isZero_of_tor Q
      P hMinimal 4 b hb hTor)

end ASGinzburg.ZAlgebra.PeriodIso
