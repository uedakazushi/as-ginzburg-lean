import ASGinzburg.GinzburgDegreeZeroAlgebra
import ASGinzburg.PathCyclicDerivativeDegrees

/-! Genuine path-valued differentials on the extended generators. The
signed extension to all paths and its square-zero proof remain separate. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

def GinzburgPath.transport {u v u' v' : Q.Vertex} (hu : u=u') (hv : v=v')
    (p : Q.GinzburgPath u v) : Q.GinzburgPath u' v' := hu ▸ hv ▸ p

@[simp] theorem GinzburgPath.cohomologicalDegree_transport {u v u' v' : Q.Vertex}
    (hu : u=u') (hv : v=v') (p : Q.GinzburgPath u v) :
    (p.transport Q hu hv).cohomologicalDegree=p.cohomologicalDegree := by subst u' v'; rfl

def originalGinzburgArrowPath (a : Q.Arrow) : Q.GinzburgPath (Q.source a) (Q.target a) :=
  .snoc (.nil (Q.source a)) (.original a) rfl

def dualGinzburgArrowPath (a : Q.Arrow) : Q.GinzburgPath (Q.target a) (Q.source a) :=
  .snoc (.nil (Q.target a)) (.dual a) rfl

noncomputable def ginzburgLoopDifferential (v : Q.Vertex) : Q.GinzburgPathComponent k v v :=
  ∑ a : Q.Arrow,
    ((if hs : Q.source a=v then Finsupp.single
      (((Q.originalGinzburgArrowPath a).comp (Q.dualGinzburgArrowPath a)).transport Q hs hs) 1 else 0)-
    (if ht : Q.target a=v then Finsupp.single
      (((Q.dualGinzburgArrowPath a).comp (Q.originalGinzburgArrowPath a)).transport Q ht ht) 1 else 0))

noncomputable def ginzburgGeneratorDifferential (φ : Q.Potential k) :
    (a : Q.GinzburgArrow) → Q.GinzburgPathComponent k (a.source Q) (a.target Q)
  | .original _ => 0
  | .dual a => Q.originalGinzburgLinearMap k (Q.target a) (Q.source a) (Q.pathCyclicDerivative k a φ)
  | .loop v => Q.ginzburgLoopDifferential k v

theorem ginzburgLoopDifferential_degree (v : Q.Vertex) :
    Q.ginzburgLoopDifferential k v ∈ Q.ginzburgCohomologicalComponent k v v (-1) := by
  unfold ginzburgLoopDifferential
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sub_mem
  · split_ifs with ht
    · apply Finsupp.single_mem_supported
      simp [GinzburgPath.cohomologicalDegree_comp,originalGinzburgArrowPath,dualGinzburgArrowPath,
        GinzburgPath.cohomologicalDegree,GinzburgArrow.cohomologicalDegree]
    · exact Submodule.zero_mem _
  · split_ifs with hs
    · apply Finsupp.single_mem_supported
      simp [GinzburgPath.cohomologicalDegree_comp,originalGinzburgArrowPath,dualGinzburgArrowPath,
        GinzburgPath.cohomologicalDegree,GinzburgArrow.cohomologicalDegree]
    · exact Submodule.zero_mem _

theorem ginzburgGeneratorDifferential_degree (φ : Q.Potential k) (a : Q.GinzburgArrow) :
    Q.ginzburgGeneratorDifferential k φ a ∈
      Q.ginzburgCohomologicalComponent k (a.source Q) (a.target Q) (a.cohomologicalDegree Q+1) := by
  cases a with
  | original a => exact Submodule.zero_mem _
  | dual a =>
    change Q.originalGinzburgLinearMap k _ _ _ ∈ Q.ginzburgCohomologicalComponent k _ _ 0
    rw [←Q.originalGinzburgLinearMap_range k]
    exact LinearMap.mem_range_self _ _
  | loop v => exact Q.ginzburgLoopDifferential_degree k v

end ASGinzburg.CutQuiver
