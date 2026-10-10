import ASGinzburg.GinzburgLoopLayerDifferential

/-! The native loop-to-dual connecting map is the actual quotient
class of the differential of each actual degree minus two representative. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgLoopDualHomology_on_representative
    (φ : Q.Potential k) (u v : Q.Vertex) (c : ℤ)
    (x : Q.ginzburgGeneratorFiltrationAtDegree k u v (-2) (-2) c) :
    Q.ginzburgGeneratorLoopToDualHomology k φ u v c
      (moduleCochainHomologyClass
        (Q.ginzburgAssociatedGradedComplex k φ u v (-2) c) (-2)
        (Submodule.Quotient.mk x) (Q.ginzburgLoopLayerQuotient_cycle k φ u v c x))=
      moduleCochainHomologyClass
        (Q.ginzburgAssociatedGradedComplex k φ u v (-1) c) (-1)
        (Submodule.Quotient.mk (Q.ginzburgLoopLayerDifferential k φ u v c x))
        (Q.ginzburgDualLayerQuotient_cycle k φ u v c
          (Q.ginzburgLoopLayerDifferential k φ u v c x)) := by
  let hS := Q.ginzburgGeneratorFilteredShortComplex_shortExact k φ u v (-2) c
  let dx := Q.ginzburgLoopLayerDifferential k φ u v c x
  let y := moduleCochainHomologyClass
    (Q.ginzburgAssociatedGradedComplex k φ u v (-2) c) (-2)
    (Submodule.Quotient.mk x) (Q.ginzburgLoopLayerQuotient_cycle k φ u v c x)
  have hx : (Q.ginzburgGeneratorFilteredShortComplex k φ u v (-2) c).g.f (-2) x=
      Submodule.Quotient.mk x := rfl
  have hdx : (Q.ginzburgGeneratorFilteredShortComplex k φ u v (-2) c).f.f (-2+1) dx=
      (Q.ginzburgGeneratorFilteredShortComplex k φ u v (-2) c).X₂.d (-2) (-2+1) x := by
    change (Submodule.inclusion
      (Q.ginzburgGeneratorFiltrationAtDegree_step_le k u v (-2) (-1) c)) dx=
      (Q.ginzburgGeneratorFilteredComplex k φ u v (-2) c).d (-2) (-2+1) x
    rw [Q.ginzburgGeneratorFilteredComplex_d k φ u v (-2) c (-2)]
    apply Subtype.ext
    rfl
  have hδ : Q.ginzburgGeneratorFiltrationConnecting k φ u v (-2) c (-2) y=
      moduleCochainHomologyClass
        (Q.ginzburgGeneratorFilteredComplex k φ u v (-1) c) (-1) dx
        (Q.ginzburgLoopLayerDifferential_cycle k φ u v c x) := by
    simpa only [ginzburgGeneratorFiltrationConnecting,show (-2:ℤ)+1=-1 by norm_num] using
      moduleCochainConnecting_class hS (-2) (Submodule.Quotient.mk x)
        (Q.ginzburgLoopLayerQuotient_cycle k φ u v c x) x hx dx hdx
  change Q.ginzburgGeneratorFilteredQuotientHomology k φ u v (-1) c (-1)
    (Q.ginzburgGeneratorFiltrationConnecting k φ u v (-2) c (-2) y)=_
  rw [hδ]
  exact moduleCochainHomologyClass_naturality
    (Q.ginzburgFilteredToAssociatedGraded k φ u v (-1) c) (-1) dx
    (Q.ginzburgLoopLayerDifferential_cycle k φ u v c x)
    (Q.ginzburgDualLayerQuotient_cycle k φ u v c dx)

end ASGinzburg.CutQuiver
