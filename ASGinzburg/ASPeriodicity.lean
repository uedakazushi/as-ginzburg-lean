import ASGinzburg.NakayamaWindowCoherence
import ASGinzburg.PeriodInverse


/-! AS regularity implies positive and negative periodicity through the constructed coherent finite-window system. -/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

/-- The finite-window algebra system is derived from the original AS conditions. -/
noncomputable def ASRegular.nakayamaWindowSystem (hAS : A.ASRegular Q) :
    A.WindowSystem (-(Q.vertices : ℤ)) where
  map l r i j hi hj := by
    simpa only [sub_eq_add_neg] using A.rightFiniteWindowNakayamaComponentEquiv Q hAS l r i j hi hj
  coherent := by
    intro l r l' r' i j hi hj hl hr
    simpa only [sub_eq_add_neg] using
      A.rightFiniteWindowNakayamaComponentEquiv_coherent Q hAS l r l' r' i j hi hj hl hr
  map_id := by
    intro l r i hi
    simpa only [sub_eq_add_neg] using A.rightFiniteWindowNakayamaComponentEquiv_id Q hAS l r i hi
  map_comp := by
    intro l r i j m hi hj hm f g
    simpa only [sub_eq_add_neg] using
      A.rightFiniteWindowNakayamaComponentEquiv_comp Q hAS l r i j m hi hj hm f g

noncomputable def ASRegular.negativePeriodIso (hAS : A.ASRegular Q) :
    A.PeriodIso (-(Q.vertices : ℤ)) := (hAS.nakayamaWindowSystem A Q).periodIso

theorem ASRegular.isPeriodic_negative (hAS : A.ASRegular Q) :
    A.IsPeriodic (-(Q.vertices : ℤ)) := ⟨hAS.negativePeriodIso A Q⟩

/-- Positive periodicity is the inverse of the proved Nakayama translation.
No periodicity or coherent window system is part of the AS hypotheses. -/
noncomputable def ASRegular.periodIso (hAS : A.ASRegular Q) : A.PeriodIso (Q.vertices : ℤ) := by
  simpa only [neg_neg] using (hAS.negativePeriodIso A Q).inverse

theorem ASRegular.isPeriodic (hAS : A.ASRegular Q) : A.IsPeriodic (Q.vertices : ℤ) :=
  ⟨hAS.periodIso A Q⟩

end ASGinzburg.ZAlgebra
