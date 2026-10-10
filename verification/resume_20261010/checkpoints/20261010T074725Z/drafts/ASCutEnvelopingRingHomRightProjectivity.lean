import ASGinzburg.AlgebraEnvelopingOppositeLeftRestriction
import work.ASGinzburgDraft.ASCutEnvelopingRingHomRightGrading

/-! The actual first-factor restriction of the native enveloping ring-Hom
complex has projective terms. Original AS regularity also gives a common
internal lower bound on its four potentially nonzero terms. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutEnvelopingMinimalRingHomRightNatComplex_term_projective
    (hAS : A.ASRegular Q) (n : ℕ) :
    Projective ((hAS.cutEnvelopingMinimalRingHomRightNatComplex A Q).X n) := by
  let R := hAS.CutGradedAlgebra A Q
  have hP : Projective ((hAS.cutEnvelopingMinimalRingHomNatComplex A Q).X n) :=
    ((ordinaryFiniteProjectiveProperty_iff _ _).mp
      (hAS.cutEnvelopingMinimalRingHomNatComplex_term_finiteProjective A Q n)).2
  change Projective ((envelopingOppositeLeftRestrictionFunctor k R).obj
    ((hAS.cutEnvelopingMinimalRingHomNatComplex A Q).X n))
  exact (envelopingOppositeLeftRestrictionFunctor k R).projective_obj_of_projective hP

theorem ASRegular.cutEnvelopingMinimalRingHomRightTermData_projective
    (hAS : A.ASRegular Q) (n : ℕ) :
    Projective (hAS.cutEnvelopingMinimalRingHomRightTermData A Q n).ringModule := by
  rw [hAS.cutEnvelopingMinimalRingHomRightTermData_ringModule A Q n]
  exact hAS.cutEnvelopingMinimalRingHomRightNatComplex_term_projective A Q n

theorem ASRegular.cutEnvelopingMinimalRingHomRightTermData_common_lower_bound
    (hAS : A.ASRegular Q) :
    ∃ b : ℤ, ∀ n : ℕ, n < 4 →
      (hAS.cutEnvelopingMinimalRingHomRightTermData A Q n).BoundedBelow b := by
  obtain ⟨b0, hb0⟩ := hAS.cutEnvelopingMinimalRingHomRightTermData_exists_lower_bound A Q 0
  obtain ⟨b1, hb1⟩ := hAS.cutEnvelopingMinimalRingHomRightTermData_exists_lower_bound A Q 1
  obtain ⟨b2, hb2⟩ := hAS.cutEnvelopingMinimalRingHomRightTermData_exists_lower_bound A Q 2
  obtain ⟨b3, hb3⟩ := hAS.cutEnvelopingMinimalRingHomRightTermData_exists_lower_bound A Q 3
  refine ⟨min (min b0 b1) (min b2 b3), ?_⟩
  intro n hn q hq
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn' with rfl | rfl | rfl | rfl
  · exact hb0 q (lt_of_lt_of_le hq (le_trans (min_le_left _ _) (min_le_left _ _)))
  · exact hb1 q (lt_of_lt_of_le hq (le_trans (min_le_left _ _) (min_le_right _ _)))
  · exact hb2 q (lt_of_lt_of_le hq (le_trans (min_le_right _ _) (min_le_left _ _)))
  · exact hb3 q (lt_of_lt_of_le hq (le_trans (min_le_right _ _) (min_le_right _ _)))

end ASGinzburg.ZAlgebra
