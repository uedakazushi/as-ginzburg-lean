import ASGinzburg.OppositeGinzburgDifferentialTransport
import ASGinzburg.GinzburgSquareProducts

/-! The generator comparison extends by the genuine graded Leibniz rule. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

set_option maxHeartbeats 800000 in
theorem oppositeGinzburgPathComponentEquiv_pathDifferential (φ : Q.Potential k)
    {u v : Q.Vertex} (p : Q.GinzburgPath u v) :
    Q.oppositeGinzburgPathComponentEquiv k u v
        (Q.ginzburgDifferential k φ u v (Finsupp.single p 1)) =
      ginzburgSign k (p.cohomologicalDegree + 1) •
        Q.opposite.ginzburgDifferential k (Q.oppositePotentialEquiv k φ) v.rev u.rev
          (Q.oppositeGinzburgPathComponentEquiv k u v (Finsupp.single p 1)) := by
  classical
  induction p with
  | nil => simp [GinzburgPath.differential_nil]
  | @snoc v p a h ih =>
    subst h
    have hpa : Finsupp.single (GinzburgPath.snoc p a rfl) (1 : k) =
        Q.ginzburgPathComp k (Finsupp.single (Q.ginzburgArrowPath a) 1)
          (Finsupp.single p 1) := by
      simp [ginzburgArrowPath, GinzburgPath.comp]
    have hdeg : (Q.ginzburgArrowPath a).cohomologicalDegree = a.cohomologicalDegree Q := by
      simp [ginzburgArrowPath, GinzburgPath.cohomologicalDegree]
    rw [hpa, Q.ginzburgDifferential_comp]
    simp only [map_add, Q.oppositeGinzburgPathComponentEquiv_comp,
      ginzburgSignMap_single, hdeg, map_smul, LinearMap.smul_apply,
      Q.oppositeGinzburgPathComponentEquiv_arrowDifferential]
    rw [ih]
    rw [Q.opposite.ginzburgDifferential_comp]
    simp only [Q.oppositeGinzburgPathComponentEquiv_single, ginzburgSignMap_single,
      GinzburgPath.opposite_cohomologicalDegree, GinzburgPath.cohomologicalDegree,
      map_smul, LinearMap.smul_apply, smul_add, smul_smul]
    simp only [ginzburgSign_add, mul_left_comm, mul_comm,
      ginzburgSign_mul_self, one_mul]
    abel

end ASGinzburg.CutQuiver
