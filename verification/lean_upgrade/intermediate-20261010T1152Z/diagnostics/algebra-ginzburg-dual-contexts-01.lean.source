import ASGinzburg.GinzburgDegreeNegOnePaths
import ASGinzburg.GinzburgBoundarySpaces

/-! Differentiating a path with a single reverse arrow inserts exactly
its actual cyclic derivative between the ordinary prefix and suffix. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgDifferential_dualContext (φ : Q.Potential k) {u v : Q.Vertex}
    (a : Q.Arrow) (l : Q.Path u (Q.target a)) (r : Q.Path (Q.source a) v) :
    Q.ginzburgDifferential k φ u v
      (Finsupp.single ((l.originalGinzburg Q).comp
        ((Q.dualGinzburgArrowPath a).comp (r.originalGinzburg Q))) 1)=
      Q.originalGinzburgLinearMap k u v
        (Q.pathComp k (Finsupp.single r 1)
          (Q.pathComp k (Q.pathCyclicDerivative k a φ) (Finsupp.single l 1))) := by
  have hs : Finsupp.single ((l.originalGinzburg Q).comp
      ((Q.dualGinzburgArrowPath a).comp (r.originalGinzburg Q))) (1:k)=
      Q.ginzburgPathComp k (Q.ginzburgPathComp k (Finsupp.single (r.originalGinzburg Q) 1)
        (Finsupp.single (Q.dualGinzburgArrowPath a) 1)) (Finsupp.single (l.originalGinzburg Q) 1) := by
    simp
  have hl : Q.ginzburgDifferential k φ _ _ (Finsupp.single (l.originalGinzburg Q) 1)=0 := by
    simpa only [originalGinzburgLinearMap_single] using Q.ginzburgDifferential_original k φ (Finsupp.single l 1)
  have hr : Q.ginzburgDifferential k φ _ _ (Finsupp.single (r.originalGinzburg Q) 1)=0 := by
    simpa only [originalGinzburgLinearMap_single] using Q.ginzburgDifferential_original k φ (Finsupp.single r 1)
  rw [hs,Q.ginzburgDifferential_comp,Q.ginzburgDifferential_comp,hl,hr,
    Q.ginzburgDifferential_dualArrow]
  simp only [map_zero,LinearMap.zero_apply,zero_add,add_zero,ginzburgSignMap_single,
    Path.originalGinzburg_cohomologicalDegree,ginzburgSign_zero,one_smul]
  rw [Q.originalGinzburgLinearMap_comp,Q.originalGinzburgLinearMap_comp,
    Q.originalGinzburgLinearMap_single,Q.originalGinzburgLinearMap_single]
  exact (Q.ginzburgPathComp_assoc k _ _ _).symm

theorem ginzburgBoundaryLift_dualContext (φ : Q.Potential k) {u v : Q.Vertex}
    (a : Q.Arrow) (l : Q.Path u (Q.target a)) (r : Q.Path (Q.source a) v)
    (hp : ((l.originalGinzburg Q).comp
      ((Q.dualGinzburgArrowPath a).comp (r.originalGinzburg Q))).cohomologicalDegree=-1) :
    Q.ginzburgBoundaryLift k φ u v ⟨Finsupp.single ((l.originalGinzburg Q).comp
      ((Q.dualGinzburgArrowPath a).comp (r.originalGinzburg Q))) 1,
        Finsupp.single_mem_supported _ _ hp⟩=
      Q.pathComp k (Finsupp.single r 1)
        (Q.pathComp k (Q.pathCyclicDerivative k a φ) (Finsupp.single l 1)) := by
  apply Q.originalGinzburgLinearMap_injective k u v
  rw [Q.originalGinzburgLinearMap_boundaryLift]
  exact Q.ginzburgDifferential_dualContext k φ a l r

end ASGinzburg.CutQuiver
