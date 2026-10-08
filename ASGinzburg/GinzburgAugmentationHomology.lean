import ASGinzburg.GinzburgAugmentationComplex

/-! Concrete cycle-boundary criterion for the genuine augmentation complex. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgAugmentationHomology_succ_isZero_iff_cycles (φ : Q.Potential k)
    (u v : Q.Vertex) (c q : ℤ) :
    IsZero (Q.ginzburgAugmentationHomology k φ u v c (q+1)) ↔
      ∀ f : Q.ginzburgAugmentationAtDegree k u v (q+1) c,
        Q.ginzburgDifferential k φ u v f.val=0 →
          ∃ g : Q.ginzburgAugmentationAtDegree k u v q c,
            Q.ginzburgDifferential k φ u v g.val=f.val := by
  let C := Q.ginzburgAugmentationCochainComplex k φ u v c
  change IsZero (C.homology (q+1)) ↔ _
  rw [←C.exactAt_iff_isZero_homology,
    C.exactAt_iff' (j:=q+1) (i:=q) (k:=q+1+1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  have hf : C.d q (q+1)=ModuleCat.ofHom (Q.ginzburgAugmentationGradedDifferential k φ u v q c) := by
    exact Q.ginzburgAugmentationCochainComplex_d k φ u v c q
  have hg : C.d (q+1) (q+1+1)=ModuleCat.ofHom (Q.ginzburgAugmentationGradedDifferential k φ u v (q+1) c) :=
    Q.ginzburgAugmentationCochainComplex_d k φ u v c (q+1)
  change (∀ f : Q.ginzburgAugmentationAtDegree k u v (q+1) c,
    C.d (q+1) (q+1+1) f=0 → ∃ g : Q.ginzburgAugmentationAtDegree k u v q c,
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
