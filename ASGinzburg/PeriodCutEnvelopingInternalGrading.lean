import ASGinzburg.PeriodCutEnvelopingIntegerMultiplication

/-! The actual ordinary enveloping ring has a genuine internal grading:
its multiplication and identity respect its integer homogeneous subspaces,
which form an internal direct-sum decomposition. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

set_option synthInstance.maxHeartbeats 200000 in
noncomputable instance cutEnvelopingIntegerGradedMonoid :
    SetLike.GradedMonoid
      (E.cutEnvelopingIntegerHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ))) where
  toGradedOne := E.cutEnvelopingIntegerGradedOne Q
  toGradedMul := E.cutEnvelopingIntegerGradedMul (fun i : Q.Vertex => (i.val : ℤ))

end ASGinzburg.ZAlgebra.PeriodIso
