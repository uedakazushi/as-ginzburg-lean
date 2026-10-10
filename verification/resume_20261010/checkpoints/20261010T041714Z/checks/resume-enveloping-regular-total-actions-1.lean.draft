import work.ASGinzburgDraft.PeriodCutEnvelopingRegularHomogeneousActions
import work.ASGinzburgDraft.PeriodCutEnvelopingDegreeInclusion

/-! The actual full enveloping action on R respects the genuine total
degree, including arbitrary finite sums within a homogeneous block. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

theorem cutEnvelopingRegularModule_totalDegree_smul (n : ℕ) (q : ℤ)
    (a : AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))))
    (ha : a ∈ E.cutEnvelopingHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ)) n)
    (x : E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))
    (hx : x ∈ E.cutIntegerHomogeneousSpace Q q) :
    letI := E.cutEnvelopingRegularModule (fun i : Q.Vertex => (i.val : ℤ))
    a • x ∈ E.cutIntegerHomogeneousSpace Q (q+(n:ℤ)) := by
  letI := E.cutEnvelopingRegularModule (fun i : Q.Vertex => (i.val : ℤ))
  obtain ⟨a,rfl⟩ := ha
  change regularEnvelopingRepresentation k _
    (E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) n a) x ∈ _
  let L := (regularEnvelopingRepresentation k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))).toLinearMap.comp
      (E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) n)
  induction a using DirectSum.induction_on with
  | zero =>
    have h : regularEnvelopingRepresentation k _
        (E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) n 0) x = 0 :=
      LinearMap.congr_fun L.map_zero x
    rw [h]
    exact Submodule.zero_mem _
  | of d a =>
    change regularEnvelopingRepresentation k _
      (E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) n
        (DirectSum.lof k (CutEnvelopingDegreePairs n)
          (fun d => E.CutEnvelopingBlock (fun i : Q.Vertex => (i.val : ℤ)) d.val) d a)) x ∈ _
    rw [E.cutEnvelopingDegreeInclusion_lof]
    simpa only [d.property] using
      E.cutEnvelopingRegularHomogeneousOperator_homogeneous Q d.val a q x hx
  | add a b ha hb =>
    have h : regularEnvelopingRepresentation k _
        (E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) n (a+b)) x =
        regularEnvelopingRepresentation k _
          (E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) n a) x +
        regularEnvelopingRepresentation k _
          (E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) n b) x :=
      LinearMap.congr_fun (L.map_add a b) x
    exact h.symm ▸ Submodule.add_mem _ ha hb

end ASGinzburg.ZAlgebra.PeriodIso
