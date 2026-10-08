import ASGinzburg.GinzburgGeneratorFilteredAugmentation

/-! Genuine Ginzburg regularity identifies the first syzygy in the
filtered homology sequence, using actual augmentation acyclicity. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem GinzburgRegular.lowestGeneratorConnecting_isIso {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (u v : Q.Vertex) (c : ℤ) :
    IsIso (Q.ginzburgGeneratorFiltrationConnecting k φ u v (-2) c (-2)) := by
  haveI : Mono (Q.ginzburgGeneratorFiltrationConnecting k φ u v (-2) c (-2)) := by
    apply (Q.ginzburgGeneratorFiltrationHomology_exact₃ k φ u v (-2) c (-2)).mono_g
    exact (h.generatorFilteredNegTwoHomology_isZero Q k u v c (-2) (by norm_num)).eq_of_src _ _
  haveI : Epi (Q.ginzburgGeneratorFiltrationConnecting k φ u v (-2) c (-2)) := by
    apply (Q.ginzburgGeneratorFiltrationHomology_exact₁ k φ u v (-2) c (-2)).epi_f
    exact (h.generatorFilteredNegTwoHomology_isZero Q k u v c (-2+1) (by norm_num)).eq_of_tgt _ _
  exact isIso_of_mono_of_epi _

noncomputable def GinzburgRegular.lowestGeneratorConnectingIso {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgAssociatedGradedHomology k φ u v (-2) c (-2) ≅
      Q.ginzburgGeneratorFilteredHomology k φ u v (-1) c (-1) := by
  letI := h.lowestGeneratorConnecting_isIso Q k u v c
  exact asIso (Q.ginzburgGeneratorFiltrationConnecting k φ u v (-2) c (-2))

end ASGinzburg.CutQuiver
