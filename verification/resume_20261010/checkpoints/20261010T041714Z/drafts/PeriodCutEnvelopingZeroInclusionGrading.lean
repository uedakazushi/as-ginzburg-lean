import work.ASGinzburgDraft.PeriodCutEnvelopingIntegerHomogeneousSubspaces
import work.ASGinzburgDraft.PeriodCutEnvelopingDegreeZeroBridge

/-! The actual degree-zero enveloping inclusion lands in degree zero of
the genuine internal grading. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

theorem cutEnvelopingZeroInclusion_mem_integerDegreeZero
    (a : AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0)) :
    E.cutEnvelopingZeroInclusion Q a ∈
      E.cutEnvelopingIntegerHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ)) 0 := by
  rw [show (0 : ℤ) = ((0:ℕ):ℤ) from rfl,
    E.cutEnvelopingIntegerHomogeneousSubspace_natCast]
  exact ⟨E.cutEnvelopingDegreeZeroEquiv Q a,
    E.cutEnvelopingDegreeInclusion_degreeZeroEquiv Q a⟩

end ASGinzburg.ZAlgebra.PeriodIso
