import ASGinzburg.GinzburgGeneratorFiltrationDifferential

/-! The actual last generators have exactly three cohomological degrees;
the last-generator filtration is exhaustive and terminates. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

theorem GinzburgArrow.cohomologicalDegree_lower (a : Q.GinzburgArrow) :
    -2 ≤ a.cohomologicalDegree Q := by
  cases a <;> simp [cohomologicalDegree]

theorem GinzburgArrow.cohomologicalDegree_upper (a : Q.GinzburgArrow) :
    a.cohomologicalDegree Q ≤ 0 := by
  cases a <;> simp [cohomologicalDegree]

theorem ginzburgGeneratorFiltrationPaths_negTwo (u v : Q.Vertex) :
    Q.ginzburgGeneratorFiltrationPaths u v (-2)={p | 0<p.length} := by
  ext p
  constructor
  · exact Q.ginzburgGeneratorFiltrationPaths_nonempty
  · intro hp
    exact ⟨p.lastGenerator Q hp,p.lastGenerator_path Q hp,
      (p.lastGenerator Q hp).1.val.cohomologicalDegree_lower Q⟩

theorem ginzburgGeneratorFiltrationPaths_one (u v : Q.Vertex) :
    Q.ginzburgGeneratorFiltrationPaths u v 1=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro p ⟨d,hd,hr⟩
  have hu := d.1.val.cohomologicalDegree_upper Q
  omega

universe u
variable (k : Type u) [Field k]

theorem ginzburgGeneratorFiltration_negTwo (u v : Q.Vertex) :
    Q.ginzburgGeneratorFiltration k u v (-2)=Q.ginzburgAugmentationSubmodule k u v := by
  unfold ginzburgGeneratorFiltration ginzburgAugmentationSubmodule
  rw [Q.ginzburgGeneratorFiltrationPaths_negTwo]

theorem ginzburgGeneratorFiltration_one (u v : Q.Vertex) :
    Q.ginzburgGeneratorFiltration k u v 1=⊥ := by
  unfold ginzburgGeneratorFiltration
  rw [Q.ginzburgGeneratorFiltrationPaths_one,Finsupp.supported_empty]

end ASGinzburg.CutQuiver
