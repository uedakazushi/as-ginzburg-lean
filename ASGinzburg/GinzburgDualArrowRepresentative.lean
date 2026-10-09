import ASGinzburg.GinzburgDualLayerDifferential

/-! A native dual arrow gives an actual filtered degree minus one
representative; its derivative is the actual original path relation. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgDualArrow_mem_filtration (a : Q.Arrow) :
    Finsupp.single (Q.ginzburgArrowPath (.dual a)) (1:k) ∈
      Q.ginzburgGeneratorFiltrationAtDegree k (Q.target a) (Q.source a)
        (-1) (-1) ((GinzburgArrow.dual a).cutDegree Q) := by
  rw [Q.ginzburgGeneratorFiltrationAtDegree_eq_inf]
  refine ⟨?_,?_,?_⟩
  · apply Finsupp.single_mem_supported
    exact ⟨⟨⟨.dual a,rfl⟩,.nil (Q.target a)⟩,rfl,by rfl⟩
  · apply Finsupp.single_mem_supported
    rfl
  · apply Finsupp.single_mem_supported
    simp [ginzburgArrowPath,GinzburgPath.cutDegree]

noncomputable def ginzburgDualArrowRepresentative (a : Q.Arrow) :
    Q.ginzburgGeneratorFiltrationAtDegree k (Q.target a) (Q.source a)
      (-1) (-1) ((GinzburgArrow.dual a).cutDegree Q) :=
  ⟨Finsupp.single (Q.ginzburgArrowPath (.dual a)) 1,Q.ginzburgDualArrow_mem_filtration k a⟩

end ASGinzburg.CutQuiver
