import ASGinzburg.GinzburgCutCochainComplex

/-! Fixed cut components have a concrete finite cohomological range,
deduced from positive winding and the genuine generator degrees. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
variable (Q : CutQuiver)

theorem GinzburgPath.cohomologicalDegree_lower_length {u v : Q.Vertex}
    (p : Q.GinzburgPath u v) : -2*(p.length:ℤ) ≤ p.cohomologicalDegree := by
  induction p with
  | nil => simp [length,cohomologicalDegree]
  | snoc p a h ih =>
    cases a <;>
      simp only [length,cohomologicalDegree,GinzburgArrow.cohomologicalDegree,
        Nat.cast_add,Nat.cast_one] <;> omega

theorem GinzburgPath.cohomologicalDegree_lower_winding {u v : Q.Vertex}
    (p : Q.GinzburgPath u v) : -2*p.winding ≤ p.cohomologicalDegree := by
  have := p.cohomologicalDegree_lower_length Q
  have := p.length_le_winding Q
  omega

theorem GinzburgPath.cohomologicalDegree_lower_cut {u v : Q.Vertex}
    (p : Q.GinzburgPath u v) :
    -2*((v.val:ℤ)-u.val+Q.vertices*p.cutDegree) ≤ p.cohomologicalDegree := by
  simpa only [p.winding_formula] using p.cohomologicalDegree_lower_winding Q

universe u
variable (k : Type u) [Field k]

theorem ginzburgCutCohomologicalComponent_eq_bot_of_lt (u v : Q.Vertex) (c q : ℤ)
    (hq : q < -2*((v.val:ℤ)-u.val+Q.vertices*c)) :
    Q.ginzburgCutCohomologicalComponent k u v q c=⊥ := by
  change Finsupp.supported k k _ ⊓ Finsupp.supported k k _=⊥
  rw [←Finsupp.supported_inter]
  have hs : {p : Q.GinzburgPath u v | p.cohomologicalDegree=q} ∩
      {p : Q.GinzburgPath u v | p.cutDegree=c}=∅ := by
    ext p
    simp only [Set.mem_inter_iff,Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
    rintro ⟨hp,hc⟩
    have h := p.cohomologicalDegree_lower_cut Q
    rw [hp,hc] at h
    omega
  rw [hs,Finsupp.supported_empty]

theorem ginzburgCutCohomologicalComponent_eq_bot_of_pos (u v : Q.Vertex) (c q : ℤ)
    (hq : 0<q) : Q.ginzburgCutCohomologicalComponent k u v q c=⊥ := by
  unfold ginzburgCutCohomologicalComponent
  rw [Q.ginzburgCohomologicalComponent_eq_bot_of_pos k u v hq,bot_inf_eq]

theorem ginzburgCutCochainTerm_isZero_of_outside (u v : Q.Vertex) (c q : ℤ)
    (hq : q < -2*((v.val:ℤ)-u.val+Q.vertices*c) ∨ 0<q) :
    IsZero (ModuleCat.of k (Q.ginzburgCutCohomologicalComponent k u v q c)) := by
  have hb : Q.ginzburgCutCohomologicalComponent k u v q c=⊥ := by
    rcases hq with hq|hq
    · exact Q.ginzburgCutCohomologicalComponent_eq_bot_of_lt k u v c q hq
    · exact Q.ginzburgCutCohomologicalComponent_eq_bot_of_pos k u v c q hq
  rw [hb]
  exact ModuleCat.isZero_of_subsingleton _

theorem ginzburgCutHomology_isZero_of_outside (φ : Q.Potential k) (u v : Q.Vertex) (c q : ℤ)
    (hq : q < -2*((v.val:ℤ)-u.val+Q.vertices*c) ∨ 0<q) :
    IsZero (Q.ginzburgCutHomology k φ u v c q) :=
  ((Q.ginzburgCutCochainComplex k φ u v c).sc q).isZero_homology_of_isZero_X₂
    (Q.ginzburgCutCochainTerm_isZero_of_outside k u v c q hq)

end ASGinzburg.CutQuiver
