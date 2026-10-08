import ASGinzburg.GinzburgGeneratorLayerHomology
import ASGinzburg.GinzburgCutBounds

/-! Each actual last-generator layer has homology concentrated in
its generator degree under genuine Ginzburg regularity. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgGeneratorPrefixTerm_isZero_of_above (u v : Q.Vertex) (r c q : ℤ)
    (hq : r<q) : IsZero (ModuleCat.of k (Q.GinzburgGeneratorPrefix k u v r q c)) := by
  letI : ∀ a : {a : Q.GinzburgArrow // a.target Q=v ∧ a.cohomologicalDegree Q=r},
      Subsingleton (Q.ginzburgCutCohomologicalComponent k u (a.val.source Q)
        (q-r) (c-a.val.cutDegree Q)) := fun a => by
    rw [Q.ginzburgCutCohomologicalComponent_eq_bot_of_pos k u (a.val.source Q)
      (c-a.val.cutDegree Q) (q-r) (by omega)]
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _

theorem ginzburgGeneratorPrefixHomology_isZero_of_above (φ : Q.Potential k)
    (u v : Q.Vertex) (r c q : ℤ) (hq : r<q) :
    IsZero (Q.ginzburgGeneratorPrefixHomology k φ u v r c q) :=
  ((Q.ginzburgGeneratorPrefixComplex k φ u v r c).sc q).isZero_homology_of_isZero_X₂
    (Q.ginzburgGeneratorPrefixTerm_isZero_of_above k u v r c q hq)

theorem ginzburgAssociatedGradedHomology_isZero_of_above (φ : Q.Potential k)
    (u v : Q.Vertex) (r c q : ℤ) (hq : r<q) :
    IsZero (Q.ginzburgAssociatedGradedHomology k φ u v r c q) :=
  (Q.ginzburgGeneratorPrefixHomology_isZero_of_above k φ u v r c q hq).of_iso
    (Q.ginzburgAssociatedGradedPrefixHomologyIso k φ u v r c q)

theorem GinzburgRegular.associatedGradedHomology_isZero_of_ne {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (u v : Q.Vertex) (r c q : ℤ) (hq : q≠r) :
    IsZero (Q.ginzburgAssociatedGradedHomology k φ u v r c q) := by
  rcases lt_or_gt_of_ne hq with hq|hq
  · exact h.associatedGradedHomology_isZero Q k u v r c q hq
  · exact Q.ginzburgAssociatedGradedHomology_isZero_of_above k φ u v r c q hq

end ASGinzburg.CutQuiver
