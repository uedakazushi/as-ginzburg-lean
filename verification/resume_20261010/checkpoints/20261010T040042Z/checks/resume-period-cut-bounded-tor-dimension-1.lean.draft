import work.ASGinzburgDraft.PeriodCutGradedBoundedMinimalResolution
import work.ASGinzburgDraft.PeriodCutGradedMinimalTorDetection

/-! Actual first-factor Tor against the genuine graded radical quotient
detects resolution terms and ordinary projective dimension for every
bounded-below native graded module. Its minimal resolution is constructed,
not postulated. The statement is confined to the native cut algebra. -/
namespace ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

theorem boundedBelowMinimalResolution_term_isZero_of_tor
    (M : E.CutGradedRightModule Q) (b : ℤ)
    (hb : ∀ q : ℤ, q < b → M.grade q = ⊥) (n : ℕ)
    (hTor : IsZero ((balancedTensorTorLeftFunctor.{u,v,v,v} k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q) n).obj M.ringModule)) :
    IsZero ((M.boundedBelowMinimalResolution b hb).complex.X n) :=
  E.cutGradedMinimalResolution_term_isZero_of_tor Q
    (M.boundedBelowMinimalResolution b hb) (M.boundedBelowMinimalResolution_all_d_minimal b hb)
    n (-(Int.natAbs ((Q.vertices:ℤ)*(-b)+(Q.vertices:ℤ)) : ℤ))
    (M.boundedBelowMinimalResolution_grade_eq_bot b hb n) hTor

theorem ordinary_hasProjectiveDimensionLE_of_boundedBelow_tor_four
    (M : E.CutGradedRightModule Q) (b : ℤ)
    (hb : ∀ q : ℤ, q < b → M.grade q = ⊥)
    (hTor : IsZero ((balancedTensorTorLeftFunctor.{u,v,v,v} k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q) 4).obj M.ringModule)) :
    HasProjectiveDimensionLE M.ringModule 3 :=
  E.cutGradedMinimalResolution_ordinary_hasProjectiveDimensionLE_of_tor_four Q
    (M.boundedBelowMinimalResolution b hb) (M.boundedBelowMinimalResolution_all_d_minimal b hb)
    (-(Int.natAbs ((Q.vertices:ℤ)*(-b)+(Q.vertices:ℤ)) : ℤ))
    (M.boundedBelowMinimalResolution_grade_eq_bot b hb 4) hTor

end ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
