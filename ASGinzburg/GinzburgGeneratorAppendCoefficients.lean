import ASGinzburg.GinzburgGeneratorLayerComparison

/-! Actual coefficients of adjoining a specified last generator:
the same generator reads its prefix, and different last generators give zero. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

def ginzburgAppendGeneratorEmbedding (a : Q.GinzburgArrow) (u : Q.Vertex) :
    Q.GinzburgPath u (a.source Q) ↪ Q.GinzburgPath u (a.target Q) where
  toFun p := GinzburgPath.snoc p a rfl
  inj' := by
    intro p q h
    have hd := GinzburgLastGeneratorData.path_injective Q u (a.target Q)
      (a₁:=⟨⟨a,rfl⟩,p⟩) (a₂:=⟨⟨a,rfl⟩,q⟩) h
    exact eq_of_heq (Sigma.mk.inj hd).2

universe u
variable (k : Type u) [Field k]

theorem ginzburgAppendGenerator_eq_embDomain (a : Q.GinzburgArrow) (u : Q.Vertex)
    (f : Q.GinzburgPathComponent k u (a.source Q)) :
    Q.ginzburgPathComp k (Finsupp.single (Q.ginzburgArrowPath a) 1) f=
      f.embDomain (Q.ginzburgAppendGeneratorEmbedding a u) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,Finsupp.embDomain_add,hf,hg]
  | single p c =>
    simp only [ginzburgPathComp_single,Finsupp.embDomain_single,one_mul]
    rfl

theorem ginzburgAppendGenerator_coefficient (a : Q.GinzburgArrow) (u : Q.Vertex)
    (f : Q.GinzburgPathComponent k u (a.source Q)) (p : Q.GinzburgPath u (a.source Q)) :
    Q.ginzburgPathComp k (Finsupp.single (Q.ginzburgArrowPath a) 1) f
      (GinzburgPath.snoc p a rfl)=f p := by
  rw [Q.ginzburgAppendGenerator_eq_embDomain]
  exact Finsupp.embDomain_apply (Q.ginzburgAppendGeneratorEmbedding a u) f p

theorem ginzburgAppendGenerator_coefficient_other (a : Q.GinzburgArrow) (u : Q.Vertex)
    (f : Q.GinzburgPathComponent k u (a.source Q))
    (d : Q.GinzburgLastGeneratorData u (a.target Q)) (hd : d.1.val≠a) :
    Q.ginzburgPathComp k (Finsupp.single (Q.ginzburgArrowPath a) 1) f (d.path Q)=0 := by
  rw [Q.ginzburgAppendGenerator_eq_embDomain]
  apply Finsupp.embDomain_notin_range
  rintro ⟨p,hp⟩
  have he := GinzburgLastGeneratorData.path_injective Q u (a.target Q)
    (a₁:=⟨⟨a,rfl⟩,p⟩) (a₂:=d) hp
  exact hd (congrArg (fun d => d.1.val) he).symm

end ASGinzburg.CutQuiver
