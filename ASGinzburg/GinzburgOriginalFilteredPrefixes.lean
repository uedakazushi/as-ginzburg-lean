import ASGinzburg.GinzburgGradedPrefixInverse
import ASGinzburg.GinzburgGeneratorUpperFiltration

/-! Actual degree-zero upper-filtered representatives have canonical
original-generator coefficients, with no change to path-length support. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgOriginalFilteredToPrefix (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgGeneratorFilteredComplex k φ u v 0 c ⟶
      Q.ginzburgGeneratorPrefixComplex k φ u v 0 c :=
  Q.ginzburgFilteredToAssociatedGraded k φ u v 0 c ≫
    (Q.ginzburgGeneratorPrefixGradedIso k φ u v 0 c).inv

theorem ginzburgOriginalFilteredToPrefix_f (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ)
    (z : Q.ginzburgGeneratorFiltrationAtDegree k u v 0 0 c) :
    (Q.ginzburgOriginalFilteredToPrefix k φ u v c).f 0 z=
      Q.ginzburgGeneratorLayerFreeEquiv k u v 0 0 c
        (Q.ginzburgGeneratorLayerQuotientEquiv k u v 0 0 c (Submodule.Quotient.mk z)) := by
  change (Q.ginzburgGeneratorPrefixGradedIso k φ u v 0 c).inv.f 0
    (Submodule.Quotient.mk z)=_
  exact Q.ginzburgGeneratorPrefixGradedIso_inv_f k φ u v 0 c 0 _

theorem ginzburgOriginalFilteredLayer_supported_length
    (u v : Q.Vertex) (c : ℤ) (n : ℕ)
    (z : Q.ginzburgGeneratorFiltrationAtDegree k u v 0 0 c)
    (hz : z.val ∈ Finsupp.supported k k {p : Q.GinzburgPath u v | n ≤ p.length}) :
    (Q.ginzburgGeneratorLayerQuotientEquiv k u v 0 0 c (Submodule.Quotient.mk z)).val ∈
      Finsupp.supported k k {p : Q.GinzburgPath u v | n ≤ p.length} := by
  classical
  rw [Q.ginzburgGeneratorLayerQuotientEquiv_coe_mk]
  apply (Finsupp.mem_supported k _).mpr
  intro p hp
  rw [Finsupp.support_filter] at hp
  exact (Finsupp.mem_supported k z.val).mp hz (Finset.mem_filter.mp hp).1

end ASGinzburg.CutQuiver
