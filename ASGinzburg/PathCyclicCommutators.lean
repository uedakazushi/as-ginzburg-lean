import ASGinzburg.VertexCyclicCommutators
import ASGinzburg.PathUnrolling

/-! The vertex commutator identity in the actual composable path algebra. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

def baseArrowPath (a : Q.Arrow) : Q.Path (Q.source a) (Q.target a) :=
  .snoc (.nil (Q.source a)) a rfl

noncomputable def transportPathComponent {u v u' v' : Q.Vertex}
    (hu : u=u') (hv : v=v') (f : Q.PathComponent k u v) : Q.PathComponent k u' v' := hu ▸ hv ▸ f

@[simp] theorem transportPathComponent_single {u v u' v' : Q.Vertex}
    (hu : u=u') (hv : v=v') (p : Q.Path u v) (c : k) :
    Q.transportPathComponent k hu hv (Finsupp.single p c)=Finsupp.single (p.transport hu hv) c := by
  subst u' v'; rfl

@[simp] theorem pathWordMap_transport {u v u' v' : Q.Vertex}
    (hu : u=u') (hv : v=v') (f : Q.PathComponent k u v) :
    Q.pathWordMap k u' v' (Q.transportPathComponent k hu hv f)=Q.pathWordMap k u v f := by
  subst u' v'; rfl

theorem pathWordMap_prepend {v : Q.Vertex} (a : Q.Arrow)
    (f : Q.PathComponent k (Q.target a) v) :
    Q.pathWordMap k (Q.source a) v (Q.pathComp k f (Finsupp.single (Q.baseArrowPath a) 1))=
      prependWord a (Q.pathWordMap k (Q.target a) v f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add,LinearMap.add_apply,hf,hg]
  | single p c =>
    simp [Path.toList_comp,baseArrowPath,Path.toList,prependWord,
      Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]

theorem pathWordMap_append {u : Q.Vertex} (a : Q.Arrow)
    (f : Q.PathComponent k u (Q.source a)) :
    Q.pathWordMap k u (Q.target a) (Q.pathComp k (Finsupp.single (Q.baseArrowPath a) 1) f)=
      appendWord a (Q.pathWordMap k u (Q.source a) f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add,hf,hg]
  | single p c =>
    simp [Path.toList_comp,baseArrowPath,Path.toList,appendWord,
      Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]

noncomputable def pathVertexCommutator (φ : Q.Potential k) (v : Q.Vertex) : Q.PathComponent k v v :=
  ∑ a : Q.Arrow,
    ((if hs : Q.source a=v then Q.transportPathComponent k hs hs
      (Q.pathComp k (Q.pathCyclicDerivative k a φ) (Finsupp.single (Q.baseArrowPath a) 1)) else 0)-
    (if ht : Q.target a=v then Q.transportPathComponent k ht ht
      (Q.pathComp k (Finsupp.single (Q.baseArrowPath a) 1) (Q.pathCyclicDerivative k a φ)) else 0))

theorem pathVertexCommutator_zero (φ : Q.Potential k) (v : Q.Vertex) :
    Q.pathVertexCommutator k φ v=0 := by
  apply Q.pathWordMap_injective k v v
  rw [map_zero]
  have hw : Q.pathWordMap k v v (Q.pathVertexCommutator k φ v)=
      ∑ a : Q.Arrow, ((if Q.source a=v then prependWord a (cyclicDerivative a φ.val) else 0)-
        (if Q.target a=v then appendWord a (cyclicDerivative a φ.val) else 0)) := by
    unfold pathVertexCommutator
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [map_sub]
    congr 1
    · by_cases hs : Q.source a=v
      · simp only [dif_pos hs,if_pos hs,pathWordMap_transport,
          Q.pathWordMap_prepend k,Q.pathWordMap_pathCyclicDerivative k]
      · simp [hs]
    · by_cases ht : Q.target a=v
      · simp only [dif_pos ht,if_pos ht,pathWordMap_transport,
          Q.pathWordMap_append k,Q.pathWordMap_pathCyclicDerivative k]
      · simp [ht]
  rw [hw]
  exact Q.cyclicDerivative_vertex_commutator k v φ

end ASGinzburg.CutQuiver
