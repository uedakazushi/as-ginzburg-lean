import ASGinzburg.GinzburgCutCochainComplex

/-! Actual vanishing homology is equivalent to the concrete cycle-boundary
criterion, for full and fixed-cut path complexes. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgCutHomology_succ_isZero_iff_cycles (φ : Q.Potential k)
    (u v : Q.Vertex) (c q : ℤ) :
    IsZero (Q.ginzburgCutHomology k φ u v c (q+1)) ↔
      ∀ f : Q.ginzburgCutCohomologicalComponent k u v (q+1) c,
        Q.ginzburgDifferential k φ u v f.val=0 →
          ∃ g : Q.ginzburgCutCohomologicalComponent k u v q c,
            Q.ginzburgDifferential k φ u v g.val=f.val := by
  let C := Q.ginzburgCutCochainComplex k φ u v c
  change IsZero (C.homology (q+1)) ↔ _
  rw [←C.exactAt_iff_isZero_homology,
    C.exactAt_iff' (j:=q+1) (i:=q) (k:=q+1+1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  have hf : C.d q (q+1)=Q.ginzburgCutCochainDifferential k φ u v q c := by
    exact Q.ginzburgCutCochainComplex_d k φ u v c q
  have hg : C.d (q+1) (q+1+1)=Q.ginzburgCutCochainDifferential k φ u v (q+1) c :=
    Q.ginzburgCutCochainComplex_d k φ u v c (q+1)
  change (∀ f : Q.ginzburgCutCohomologicalComponent k u v (q+1) c,
    C.d (q+1) (q+1+1) f=0 → ∃ g : Q.ginzburgCutCohomologicalComponent k u v q c,
      C.d q (q+1) g=f) ↔ _
  rw [hf,hg]
  constructor
  · intro h f hf
    obtain ⟨g,hg⟩ := h f (Subtype.ext hf)
    exact ⟨g,congrArg Subtype.val hg⟩
  · intro h f hf
    obtain ⟨g,hg⟩ := h f (congrArg Subtype.val hf)
    exact ⟨g,Subtype.ext hg⟩

theorem ginzburgHomology_succ_isZero_iff_cycles (φ : Q.Potential k) (u v : Q.Vertex) (q : ℤ) :
    IsZero (Q.ginzburgHomology k φ u v (q+1)) ↔
      ∀ f : Q.ginzburgCohomologicalComponent k u v (q+1),
        Q.ginzburgDifferential k φ u v f.val=0 →
          ∃ g : Q.ginzburgCohomologicalComponent k u v q,
            Q.ginzburgDifferential k φ u v g.val=f.val := by
  let C := Q.ginzburgCochainComplex k φ u v
  change IsZero (C.homology (q+1)) ↔ _
  rw [←C.exactAt_iff_isZero_homology,
    C.exactAt_iff' (j:=q+1) (i:=q) (k:=q+1+1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  have hf : C.d q (q+1)=Q.ginzburgCochainDifferential k φ u v q := by
    exact Q.ginzburgCochainComplex_d k φ u v q
  have hg : C.d (q+1) (q+1+1)=Q.ginzburgCochainDifferential k φ u v (q+1) :=
    Q.ginzburgCochainComplex_d k φ u v (q+1)
  change (∀ f : Q.ginzburgCohomologicalComponent k u v (q+1),
    C.d (q+1) (q+1+1) f=0 → ∃ g : Q.ginzburgCohomologicalComponent k u v q,
      C.d q (q+1) g=f) ↔ _
  rw [hf,hg]
  constructor
  · intro h f hf
    obtain ⟨g,hg⟩ := h f (Subtype.ext hf)
    exact ⟨g,congrArg Subtype.val hg⟩
  · intro h f hf
    obtain ⟨g,hg⟩ := h f (congrArg Subtype.val hf)
    exact ⟨g,Subtype.ext hg⟩

end ASGinzburg.CutQuiver
