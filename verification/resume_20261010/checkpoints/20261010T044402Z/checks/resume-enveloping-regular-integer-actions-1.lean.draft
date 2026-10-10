import work.ASGinzburgDraft.PeriodCutEnvelopingRegularTotalActions
import work.ASGinzburgDraft.PeriodCutEnvelopingIntegerHomogeneousSubspaces

/-! The genuine multiplication bimodule carries the full integer graded
action of the actual unsigned enveloping ring. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

theorem cutEnvelopingRegularModule_integerDegree_smul (p q : ℤ)
    (a : AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))))
    (ha : a ∈ E.cutEnvelopingIntegerHomogeneousSubspace
      (fun i : Q.Vertex => (i.val : ℤ)) p)
    (x : E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))
    (hx : x ∈ E.cutIntegerHomogeneousSpace Q q) :
    letI := E.cutEnvelopingRegularModule (fun i : Q.Vertex => (i.val : ℤ))
    a • x ∈ E.cutIntegerHomogeneousSpace Q (p+q) := by
  letI := E.cutEnvelopingRegularModule (fun i : Q.Vertex => (i.val : ℤ))
  by_cases hp : 0 ≤ p
  · have hn := Int.toNat_of_nonneg hp
    rw [← hn, E.cutEnvelopingIntegerHomogeneousSubspace_natCast] at ha
    simpa only [hn, add_comm] using
      E.cutEnvelopingRegularModule_totalDegree_smul Q p.toNat q a ha x hx
  · rw [E.cutEnvelopingIntegerHomogeneousSubspace_neg
      (fun i : Q.Vertex => (i.val : ℤ)) p (lt_of_not_ge hp)] at ha
    have ha0 : a = 0 := ha
    subst a
    rw [zero_smul]
    exact Submodule.zero_mem _

end ASGinzburg.ZAlgebra.PeriodIso
