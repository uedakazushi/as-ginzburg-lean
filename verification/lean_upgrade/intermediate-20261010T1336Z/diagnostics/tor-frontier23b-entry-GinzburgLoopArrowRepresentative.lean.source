import ASGinzburg.GinzburgLoopLayerDifferential

/-! A native loop gives a genuine bottom filtered representative,
whose intrinsic derivative is precisely the actual loop commutator sum. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgLoopArrow_mem_filtration (v : Q.Vertex) :
    Finsupp.single (Q.ginzburgArrowPath (.loop v)) (1:k) ∈
      Q.ginzburgGeneratorFiltrationAtDegree k v v (-2) (-2) 1 := by
  rw [Q.ginzburgGeneratorFiltrationAtDegree_eq_inf]
  refine ⟨?_,?_,?_⟩
  · apply Finsupp.single_mem_supported
    exact ⟨⟨⟨.loop v,rfl⟩,.nil v⟩,rfl,by rfl⟩
  · apply Finsupp.single_mem_supported
    rfl
  · apply Finsupp.single_mem_supported
    rfl

noncomputable def ginzburgLoopArrowRepresentative (v : Q.Vertex) :
    Q.ginzburgGeneratorFiltrationAtDegree k v v (-2) (-2) 1 :=
  ⟨Finsupp.single (Q.ginzburgArrowPath (.loop v)) 1,Q.ginzburgLoopArrow_mem_filtration k v⟩

theorem ginzburgLoopArrowDifferential_val (φ : Q.Potential k) (v : Q.Vertex) :
    (Q.ginzburgLoopLayerDifferential k φ v v 1
      (Q.ginzburgLoopArrowRepresentative k v)).val=Q.ginzburgLoopDifferential k v := by
  exact Q.ginzburgDifferential_generator k φ (.loop v)

end ASGinzburg.CutQuiver
