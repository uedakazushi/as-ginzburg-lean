import ASGinzburg.GinzburgRegularity

/-! The actual path complex has no positive-degree terms or homology;
negative regularity is therefore equivalent to homology concentrated at zero. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgCochainTerm_isZero_of_pos (u v : Q.Vertex) {q : ℤ} (hq : 0<q) :
    IsZero (ModuleCat.of k (Q.ginzburgCohomologicalComponent k u v q)) := by
  rw [Q.ginzburgCohomologicalComponent_eq_bot_of_pos k u v hq]
  exact ModuleCat.isZero_of_subsingleton _

theorem ginzburgHomology_isZero_of_pos (φ : Q.Potential k) (u v : Q.Vertex)
    {q : ℤ} (hq : 0<q) : IsZero (Q.ginzburgHomology k φ u v q) :=
  ((Q.ginzburgCochainComplex k φ u v).sc q).isZero_homology_of_isZero_X₂
    (Q.ginzburgCochainTerm_isZero_of_pos k u v hq)

theorem ginzburgTotalHomology_isZero_of_pos (φ : Q.Potential k) {q : ℤ} (hq : 0<q) :
    IsZero (Q.ginzburgTotalHomology k φ q) :=
  (Q.ginzburgTotalHomology_isZero_iff k φ q).mpr
    (fun u v => Q.ginzburgHomology_isZero_of_pos k φ u v hq)

theorem ginzburgRegular_iff_concentrated_zero (φ : Q.Potential k) :
    Q.GinzburgRegular k φ ↔ ∀ q : ℤ, q≠0 → IsZero (Q.ginzburgTotalHomology k φ q) := by
  constructor
  · intro h q hq
    by_cases hn : q<0
    · exact h q hn
    · exact Q.ginzburgTotalHomology_isZero_of_pos k φ (by omega)
  · intro h q hq
    exact h q (by omega)

end ASGinzburg.CutQuiver
