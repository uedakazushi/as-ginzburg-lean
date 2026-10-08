import ASGinzburg.PathCyclicCommutators
import ASGinzburg.GinzburgSquareProducts
import ASGinzburg.GinzburgDegreeZeroDifferential

/-! The actual square of every loop generator vanishes by the proved
vertex cyclic commutator identity, with the original signs in (1.3). -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

@[simp] theorem originalGinzburgLinearMap_baseArrow (a : Q.Arrow) :
    Q.originalGinzburgLinearMap k _ _ (Finsupp.single (Q.baseArrowPath a) 1)=
      Finsupp.single (Q.originalGinzburgArrowPath a) 1 := by
  simp [baseArrowPath,Path.originalGinzburg,originalGinzburgArrowPath]

@[simp] theorem ginzburgDifferential_originalArrow (φ : Q.Potential k) (a : Q.Arrow) :
    Q.ginzburgDifferential k φ (Q.source a) (Q.target a)
      (Finsupp.single (Q.originalGinzburgArrowPath a) 1)=0 := by
  change Q.ginzburgDifferential k φ _ _ (Finsupp.single (Q.ginzburgArrowPath (.original a)) 1)=0
  rw [Q.ginzburgDifferential_generator]
  rfl

@[simp] theorem ginzburgDifferential_dualArrow (φ : Q.Potential k) (a : Q.Arrow) :
    Q.ginzburgDifferential k φ (Q.target a) (Q.source a)
      (Finsupp.single (Q.dualGinzburgArrowPath a) 1)=
        Q.originalGinzburgLinearMap k _ _ (Q.pathCyclicDerivative k a φ) := by
  change Q.ginzburgDifferential k φ _ _ (Finsupp.single (Q.ginzburgArrowPath (.dual a)) 1)=_
  rw [Q.ginzburgDifferential_generator]
  rfl

theorem ginzburgDifferential_originalDual (φ : Q.Potential k) (a : Q.Arrow) :
    Q.ginzburgDifferential k φ (Q.source a) (Q.source a)
      (Finsupp.single ((Q.originalGinzburgArrowPath a).comp (Q.dualGinzburgArrowPath a)) 1)=
        Q.originalGinzburgLinearMap k _ _
          (Q.pathComp k (Q.pathCyclicDerivative k a φ) (Finsupp.single (Q.baseArrowPath a) 1)) := by
  have hs : Finsupp.single ((Q.originalGinzburgArrowPath a).comp (Q.dualGinzburgArrowPath a)) (1:k)=
      Q.ginzburgPathComp k (Finsupp.single (Q.dualGinzburgArrowPath a) 1)
        (Finsupp.single (Q.originalGinzburgArrowPath a) 1) := by simp
  rw [hs,Q.ginzburgDifferential_comp]
  simp only [ginzburgDifferential_originalArrow,ginzburgDifferential_dualArrow,
    map_zero,add_zero,Q.originalGinzburgLinearMap_comp,originalGinzburgLinearMap_baseArrow]

theorem ginzburgDifferential_dualOriginal (φ : Q.Potential k) (a : Q.Arrow) :
    Q.ginzburgDifferential k φ (Q.target a) (Q.target a)
      (Finsupp.single ((Q.dualGinzburgArrowPath a).comp (Q.originalGinzburgArrowPath a)) 1)=
        Q.originalGinzburgLinearMap k _ _
          (Q.pathComp k (Finsupp.single (Q.baseArrowPath a) 1) (Q.pathCyclicDerivative k a φ)) := by
  have hs : Finsupp.single ((Q.dualGinzburgArrowPath a).comp (Q.originalGinzburgArrowPath a)) (1:k)=
      Q.ginzburgPathComp k (Finsupp.single (Q.originalGinzburgArrowPath a) 1)
        (Finsupp.single (Q.dualGinzburgArrowPath a) 1) := by simp
  rw [hs,Q.ginzburgDifferential_comp]
  simp only [ginzburgDifferential_originalArrow,ginzburgDifferential_dualArrow,
    map_zero,LinearMap.zero_apply,zero_add,ginzburgSignMap_single]
  have hz : (Q.originalGinzburgArrowPath a).cohomologicalDegree=0 := rfl
  rw [hz,ginzburgSign_zero,one_smul,Q.originalGinzburgLinearMap_comp,
    Q.originalGinzburgLinearMap_baseArrow]

theorem ginzburgLoopDifferential_square_as_commutator (φ : Q.Potential k) (v : Q.Vertex) :
    Q.ginzburgDifferential k φ v v (Q.ginzburgLoopDifferential k v)=
      Q.originalGinzburgLinearMap k v v (Q.pathVertexCommutator k φ v) := by
  unfold ginzburgLoopDifferential pathVertexCommutator
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_sub,map_sub]
  congr 1
  · split_ifs with hs
    · subst v
      simpa only [GinzburgPath.transport,transportPathComponent] using
        Q.ginzburgDifferential_originalDual k φ a
    · simp
  · split_ifs with ht
    · subst v
      simpa only [GinzburgPath.transport,transportPathComponent] using
        Q.ginzburgDifferential_dualOriginal k φ a
    · simp

theorem ginzburgLoopDifferential_square (φ : Q.Potential k) (v : Q.Vertex) :
    Q.ginzburgDifferential k φ v v (Q.ginzburgLoopDifferential k v)=0 := by
  rw [Q.ginzburgLoopDifferential_square_as_commutator k φ v,
    Q.pathVertexCommutator_zero k φ v,map_zero]

theorem ginzburgGeneratorDifferential_square (φ : Q.Potential k) (a : Q.GinzburgArrow) :
    Q.ginzburgDifferential k φ (a.source Q) (a.target Q)
      (Q.ginzburgGeneratorDifferential k φ a)=0 := by
  cases a with
  | original a => exact Q.ginzburgGeneratorDifferential_original_square k φ a
  | dual a => exact Q.ginzburgGeneratorDifferential_dual_square k φ a
  | loop v => exact Q.ginzburgLoopDifferential_square k φ v

end ASGinzburg.CutQuiver
